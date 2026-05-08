#!/usr/bin/env python3
"""
meowster — local "AI JLP trading bot" (paper-trading) with an HTTP API.

Design goals:
- No private keys, no on-chain signing, no custody. Paper-trading / simulation only.
- Standard-library only (portable).
- Deterministic, testable components (indicators, portfolio, execution simulator).
- Local HTTP server for the Kasha web UI.
"""

from __future__ import annotations

import argparse
import base64
import contextlib
import dataclasses
import datetime as _dt
import decimal
import hashlib
import hmac
import http.server
import io
import json
import logging
import math
import os
import queue
import random
import signal
import sqlite3
import statistics
import threading
import time
import traceback
import typing as t
import urllib.parse
import uuid


JSON = t.Dict[str, t.Any]


def utc_now() -> _dt.datetime:
    return _dt.datetime.now(tz=_dt.timezone.utc)


def iso(ts: _dt.datetime | None = None) -> str:
    if ts is None:
        ts = utc_now()
    return ts.astimezone(_dt.timezone.utc).isoformat().replace("+00:00", "Z")


def clamp(x: float, lo: float, hi: float) -> float:
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def bps_to_frac(bps: float) -> float:
    return bps / 10_000.0


def stable_hash(obj: t.Any) -> str:
    raw = json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(raw).hexdigest()


def parse_float(s: str, *, default: float | None = None) -> float | None:
    s = s.strip()
    if not s:
        return default
    try:
        return float(s)
    except ValueError:
        return default


def parse_int(s: str, *, default: int | None = None) -> int | None:
    s = s.strip()
    if not s:
        return default
    try:
        return int(s)
    except ValueError:
        return default


def to_decimal(x: float) -> decimal.Decimal:
    return decimal.Decimal(str(x))


def money(x: float, digits: int = 2) -> float:
    q = 10 ** digits
    return math.floor(x * q + 0.5) / q


class MeowsterError(Exception):
    pass


class ConfigError(MeowsterError):
    pass


class MarketDataError(MeowsterError):
    pass


class StrategyError(MeowsterError):
    pass


class StorageError(MeowsterError):
    pass


@dataclasses.dataclass(frozen=True)
class Candle:
    ts: int  # unix seconds
    open: float
    high: float
    low: float
    close: float
    volume: float

    def typical_price(self) -> float:
        return (self.high + self.low + self.close) / 3.0


@dataclasses.dataclass(frozen=True)
class Quote:
    ts: int
    price: float
    spread_bps: float


@dataclasses.dataclass(frozen=True)
class Symbol:
    base: str
    quote: str

    @property
    def id(self) -> str:
        return f"{self.base}/{self.quote}"


@dataclasses.dataclass(frozen=True)
class Order:
    order_id: str
    symbol: str
    side: str  # "buy" | "sell"
    qty: float
    limit_price: float | None
    time_in_force: str  # "IOC" | "GTC"
    created_ts: int
    client_tag: str


@dataclasses.dataclass(frozen=True)
class Fill:
    order_id: str
    symbol: str
    side: str
    qty: float
    price: float
    fee: float
    ts: int
    liquidity: str  # "maker" | "taker"


@dataclasses.dataclass
class Position:
    symbol: str
    qty: float = 0.0
    avg_price: float = 0.0  # in quote asset
    realized_pnl: float = 0.0

    def apply_fill(self, fill: Fill) -> None:
        if fill.symbol != self.symbol:
            raise ValueError("symbol mismatch")
        signed_qty = fill.qty if fill.side == "buy" else -fill.qty
        new_qty = self.qty + signed_qty
        if abs(new_qty) < 1e-12:
            # closing out
            pnl = 0.0
            if self.qty > 0 and fill.side == "sell":
                pnl = (fill.price - self.avg_price) * fill.qty
            elif self.qty < 0 and fill.side == "buy":
                pnl = (self.avg_price - fill.price) * fill.qty
            self.realized_pnl += pnl - fill.fee
            self.qty = 0.0
            self.avg_price = 0.0
            return

        # increasing or flipping
        if self.qty == 0.0 or (self.qty > 0 and signed_qty > 0) or (self.qty < 0 and signed_qty < 0):
            # same direction: update VWAP average
            total_cost = self.avg_price * abs(self.qty) + fill.price * abs(signed_qty)
            total_qty = abs(self.qty) + abs(signed_qty)
            self.avg_price = total_cost / max(total_qty, 1e-12)
            self.qty = new_qty
            self.realized_pnl -= fill.fee
            return

        # reducing or flipping direction: realize PnL on closed portion
        closed = min(abs(self.qty), abs(signed_qty))
        pnl = 0.0
        if self.qty > 0 and fill.side == "sell":
            pnl = (fill.price - self.avg_price) * closed
        elif self.qty < 0 and fill.side == "buy":
            pnl = (self.avg_price - fill.price) * closed
        self.realized_pnl += pnl - fill.fee
        self.qty = new_qty
        if (self.qty > 0 and self.avg_price == 0.0) or (self.qty < 0 and self.avg_price == 0.0):
            self.avg_price = fill.price


@dataclasses.dataclass
class Portfolio:
    cash: float
    positions: dict[str, Position] = dataclasses.field(default_factory=dict)
    equity_curve: list[tuple[int, float]] = dataclasses.field(default_factory=list)
    fees_paid: float = 0.0

    def get_pos(self, symbol: str) -> Position:
        p = self.positions.get(symbol)
        if p is None:
            p = Position(symbol=symbol)
            self.positions[symbol] = p
        return p

    def apply_fill(self, fill: Fill) -> None:
        p = self.get_pos(fill.symbol)
        p.apply_fill(fill)
        notional = fill.qty * fill.price
        if fill.side == "buy":
            self.cash -= notional + fill.fee
        else:
            self.cash += notional - fill.fee
        self.fees_paid += fill.fee

    def mark_to_market(self, ts: int, prices: dict[str, float]) -> float:
        eq = self.cash
        for sym, pos in self.positions.items():
            px = prices.get(sym)
            if px is None:
                continue
            eq += pos.qty * px
        self.equity_curve.append((ts, eq))
        return eq


class Indicators:
    @staticmethod
    def sma(values: list[float], window: int) -> list[float | None]:
        if window <= 0:
            raise ValueError("window")
        out: list[float | None] = [None] * len(values)
        s = 0.0
        q: queue.SimpleQueue[float] = queue.SimpleQueue()
        count = 0
        for i, v in enumerate(values):
            s += v
            q.put(v)
            count += 1
            if count > window:
                s -= q.get()
                count -= 1
            if count == window:
                out[i] = s / window
        return out

    @staticmethod
    def ema(values: list[float], window: int) -> list[float | None]:
        if window <= 0:
            raise ValueError("window")
        out: list[float | None] = [None] * len(values)
        k = 2.0 / (window + 1.0)
        ema: float | None = None
        for i, v in enumerate(values):
            if ema is None:
                ema = v
            else:
                ema = (v - ema) * k + ema
            if i + 1 >= window:
                out[i] = ema
        return out

    @staticmethod
    def rsi(closes: list[float], window: int = 14) -> list[float | None]:
        if window <= 1:
            raise ValueError("window")
        out: list[float | None] = [None] * len(closes)
        gains: list[float] = []
        losses: list[float] = []
        for i in range(1, len(closes)):
            d = closes[i] - closes[i - 1]
            gains.append(max(d, 0.0))
            losses.append(max(-d, 0.0))
        if len(gains) < window:
            return out
        avg_gain = sum(gains[:window]) / window
        avg_loss = sum(losses[:window]) / window
        rs = avg_gain / max(avg_loss, 1e-12)
        out[window] = 100.0 - (100.0 / (1.0 + rs))
        for i in range(window + 1, len(closes)):
            g = gains[i - 1]
            l = losses[i - 1]
            avg_gain = (avg_gain * (window - 1) + g) / window
            avg_loss = (avg_loss * (window - 1) + l) / window
            rs = avg_gain / max(avg_loss, 1e-12)
            out[i] = 100.0 - (100.0 / (1.0 + rs))
        return out

    @staticmethod
    def atr(candles: list[Candle], window: int = 14) -> list[float | None]:
        if window <= 1:
            raise ValueError("window")
        out: list[float | None] = [None] * len(candles)
        trs: list[float] = []
        for i, c in enumerate(candles):
            if i == 0:
                tr = c.high - c.low
            else:
                prev = candles[i - 1].close
                tr = max(c.high - c.low, abs(c.high - prev), abs(c.low - prev))
            trs.append(tr)
        if len(trs) < window:
            return out
        avg = sum(trs[:window]) / window
        out[window - 1] = avg
        for i in range(window, len(trs)):
            avg = (avg * (window - 1) + trs[i]) / window
            out[i] = avg
        return out

    @staticmethod
    def zscore(values: list[float], window: int) -> list[float | None]:
        if window <= 1:
            raise ValueError("window")
        out: list[float | None] = [None] * len(values)
        for i in range(len(values)):
            if i + 1 < window:
                continue
            slice_ = values[i + 1 - window : i + 1]
            mu = statistics.fmean(slice_)
            sd = statistics.pstdev(slice_) or 1e-12
            out[i] = (values[i] - mu) / sd
        return out


@dataclasses.dataclass(frozen=True)
class RiskLimits:
    max_pos_notional: float
    max_order_notional: float
    max_daily_loss: float
    max_leverage_soft: float
    slippage_bps: float
    fee_bps: float
    spread_bps: float

    def as_json(self) -> JSON:
        return dataclasses.asdict(self)


@dataclasses.dataclass(frozen=True)
class StrategyConfig:
    name: str
    mode: str  # "momentum" | "mean_revert" | "blend"
    ema_fast: int
    ema_slow: int
    rsi_window: int
    rsi_buy_below: float
    rsi_sell_above: float
    z_window: int
    z_enter: float
    z_exit: float
    target_pos_notional: float
    rebalance_bps: float

    def as_json(self) -> JSON:
        return dataclasses.asdict(self)


@dataclasses.dataclass(frozen=True)
class AppConfig:
    appname: str
    instance_id: str
    listen_host: str
    listen_port: int
    db_path: str
    data_path: str
    symbol: str
    base_ccy: str
    quote_ccy: str
    seed: int
    risk: RiskLimits
    strat: StrategyConfig

    def as_json(self) -> JSON:
        d = dataclasses.asdict(self)
        d["risk"] = self.risk.as_json()
        d["strat"] = self.strat.as_json()
        return d


def default_config() -> AppConfig:
    seed = 143_091_731
    rid = uuid.uuid4().hex
    risk = RiskLimits(
        max_pos_notional=1_250.0,
        max_order_notional=420.0,
        max_daily_loss=145.0,
        max_leverage_soft=1.8,
        slippage_bps=45.0,
        fee_bps=9.0,
        spread_bps=12.0,
    )
    strat = StrategyConfig(
        name="jlp_motivater_blend",
        mode="blend",
        ema_fast=14,
        ema_slow=55,
        rsi_window=14,
        rsi_buy_below=36.5,
        rsi_sell_above=66.5,
        z_window=36,
        z_enter=1.15,
        z_exit=0.35,
        target_pos_notional=600.0,
        rebalance_bps=95.0,
    )
    return AppConfig(
        appname="meowster",
        instance_id=rid,
        listen_host="127.0.0.1",
        listen_port=8844,
        db_path=os.path.join(os.getcwd(), "meowster.sqlite3"),
        data_path=os.path.join(os.getcwd(), "data.csv"),
        symbol="JLP/USDT",
        base_ccy="JLP",
        quote_ccy="USDT",
        seed=seed,
        risk=risk,
        strat=strat,
    )


class SqliteStore:
    def __init__(self, path: str):
        self.path = path
        self._lock = threading.Lock()
        self._conn = sqlite3.connect(self.path, check_same_thread=False)
        self._conn.row_factory = sqlite3.Row
        self._init_schema()

    def close(self) -> None:
        with contextlib.suppress(Exception):
            self._conn.close()

    def _init_schema(self) -> None:
        ddl = """
        PRAGMA journal_mode=WAL;
        PRAGMA synchronous=NORMAL;
        PRAGMA temp_store=MEMORY;

        CREATE TABLE IF NOT EXISTS meta (
            k TEXT PRIMARY KEY,
            v TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS candles (
            ts INTEGER PRIMARY KEY,
            open REAL NOT NULL,
            high REAL NOT NULL,
            low REAL NOT NULL,
            close REAL NOT NULL,
            volume REAL NOT NULL
        );

        CREATE TABLE IF NOT EXISTS fills (
            fill_id TEXT PRIMARY KEY,
            order_id TEXT NOT NULL,
            symbol TEXT NOT NULL,
            side TEXT NOT NULL,
            qty REAL NOT NULL,
            price REAL NOT NULL,
            fee REAL NOT NULL,
            ts INTEGER NOT NULL,
            liquidity TEXT NOT NULL
        );

        CREATE TABLE IF NOT EXISTS orders (
            order_id TEXT PRIMARY KEY,
            symbol TEXT NOT NULL,
            side TEXT NOT NULL,
            qty REAL NOT NULL,
            limit_price REAL,
            tif TEXT NOT NULL,
            created_ts INTEGER NOT NULL,
            client_tag TEXT NOT NULL,
            status TEXT NOT NULL,
            filled_qty REAL NOT NULL,
            avg_price REAL NOT NULL,
            updated_ts INTEGER NOT NULL
        );

        CREATE INDEX IF NOT EXISTS idx_fills_ts ON fills(ts);
        CREATE INDEX IF NOT EXISTS idx_orders_ts ON orders(created_ts);
        """
        with self._lock:
            self._conn.executescript(ddl)
            self._conn.commit()

    def set_meta(self, k: str, v: str) -> None:
        with self._lock:
            self._conn.execute("INSERT INTO meta(k, v) VALUES(?, ?) ON CONFLICT(k) DO UPDATE SET v=excluded.v", (k, v))
            self._conn.commit()

    def get_meta(self, k: str) -> str | None:
        with self._lock:
            cur = self._conn.execute("SELECT v FROM meta WHERE k=?", (k,))
            row = cur.fetchone()
            return None if row is None else str(row["v"])

    def upsert_candles(self, candles: list[Candle]) -> None:
        with self._lock:
            self._conn.executemany(
                "INSERT INTO candles(ts, open, high, low, close, volume) VALUES(?, ?, ?, ?, ?, ?) "
                "ON CONFLICT(ts) DO UPDATE SET open=excluded.open, high=excluded.high, low=excluded.low, close=excluded.close, volume=excluded.volume",
                [(c.ts, c.open, c.high, c.low, c.close, c.volume) for c in candles],
            )
            self._conn.commit()

    def load_candles(self, *, limit: int | None = None) -> list[Candle]:
        q = "SELECT ts, open, high, low, close, volume FROM candles ORDER BY ts ASC"
        params: tuple[t.Any, ...] = ()
        if limit is not None:
            q += " LIMIT ?"
            params = (int(limit),)
        with self._lock:
            cur = self._conn.execute(q, params)
            rows = cur.fetchall()
        return [Candle(int(r["ts"]), float(r["open"]), float(r["high"]), float(r["low"]), float(r["close"]), float(r["volume"])) for r in rows]

    def insert_order(self, order: Order) -> None:
        now = int(time.time())
        with self._lock:
            self._conn.execute(
                "INSERT INTO orders(order_id, symbol, side, qty, limit_price, tif, created_ts, client_tag, status, filled_qty, avg_price, updated_ts) "
                "VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (
                    order.order_id,
                    order.symbol,
                    order.side,
                    order.qty,
                    order.limit_price,
                    order.time_in_force,
                    order.created_ts,
                    order.client_tag,
                    "open",
                    0.0,
                    0.0,
                    now,
                ),
            )
            self._conn.commit()

    def update_order_fill(self, order_id: str, filled_qty: float, avg_price: float, status: str) -> None:
        now = int(time.time())
        with self._lock:
            self._conn.execute(
                "UPDATE orders SET filled_qty=?, avg_price=?, status=?, updated_ts=? WHERE order_id=?",
                (filled_qty, avg_price, status, now, order_id),
            )
            self._conn.commit()

    def list_orders(self, *, limit: int = 200) -> list[JSON]:
        with self._lock:
            cur = self._conn.execute(
                "SELECT order_id, symbol, side, qty, limit_price, tif, created_ts, client_tag, status, filled_qty, avg_price, updated_ts "
                "FROM orders ORDER BY created_ts DESC LIMIT ?",
                (int(limit),),
            )
            rows = cur.fetchall()
        out: list[JSON] = []
        for r in rows:
            out.append(
                {
                    "order_id": r["order_id"],
                    "symbol": r["symbol"],
                    "side": r["side"],
                    "qty": float(r["qty"]),
                    "limit_price": None if r["limit_price"] is None else float(r["limit_price"]),
                    "tif": r["tif"],
                    "created_ts": int(r["created_ts"]),
                    "client_tag": r["client_tag"],
                    "status": r["status"],
                    "filled_qty": float(r["filled_qty"]),
                    "avg_price": float(r["avg_price"]),
                    "updated_ts": int(r["updated_ts"]),
                }
            )
        return out

    def insert_fill(self, fill: Fill) -> None:
        fill_id = uuid.uuid4().hex
        with self._lock:
            self._conn.execute(
                "INSERT INTO fills(fill_id, order_id, symbol, side, qty, price, fee, ts, liquidity) VALUES(?, ?, ?, ?, ?, ?, ?, ?, ?)",
                (fill_id, fill.order_id, fill.symbol, fill.side, fill.qty, fill.price, fill.fee, fill.ts, fill.liquidity),
            )
            self._conn.commit()

    def list_fills(self, *, limit: int = 500) -> list[JSON]:
        with self._lock:
            cur = self._conn.execute(
                "SELECT order_id, symbol, side, qty, price, fee, ts, liquidity FROM fills ORDER BY ts DESC LIMIT ?",
                (int(limit),),
            )
            rows = cur.fetchall()
        return [
            {
                "order_id": r["order_id"],
                "symbol": r["symbol"],
                "side": r["side"],
                "qty": float(r["qty"]),
                "price": float(r["price"]),
                "fee": float(r["fee"]),
                "ts": int(r["ts"]),
                "liquidity": r["liquidity"],
            }
            for r in rows
        ]


class CsvMarketData:
    """
    Reads OHLCV candles from a CSV file.

    Format:
      ts,open,high,low,close,volume
    where ts is unix seconds (UTC).
    """

    def __init__(self, path: str):
        self.path = path

    def load(self) -> list[Candle]:
        if not os.path.exists(self.path):
            raise MarketDataError(f"missing CSV: {self.path}")
        buf = []
        with open(self.path, "r", encoding="utf-8") as f:
            for line_no, line in enumerate(f, start=1):
                line = line.strip()
                if not line:
                    continue
                if line_no == 1 and ("ts" in line.lower() and "open" in line.lower()):
                    continue
                parts = [p.strip() for p in line.split(",")]
                if len(parts) < 6:
                    raise MarketDataError(f"bad CSV line {line_no}: {line}")
                ts = int(float(parts[0]))
                o = float(parts[1])
                h = float(parts[2])
                l = float(parts[3])
                c = float(parts[4])
                v = float(parts[5])
                buf.append(Candle(ts, o, h, l, c, v))
        buf.sort(key=lambda x: x.ts)
        return buf


@dataclasses.dataclass(frozen=True)
class Signal:
    ts: int
    action: str  # "hold" | "buy" | "sell"
    strength: float  # 0..1
    reason: str

    def as_json(self) -> JSON:
        return dataclasses.asdict(self)


class BlendStrategy:
    def __init__(self, cfg: StrategyConfig):
        self.cfg = cfg

    def _momentum(self, closes: list[float]) -> list[Signal | None]:
        fast = Indicators.ema(closes, self.cfg.ema_fast)
        slow = Indicators.ema(closes, self.cfg.ema_slow)
        out: list[Signal | None] = [None] * len(closes)
        for i in range(len(closes)):
            if fast[i] is None or slow[i] is None:
                continue
            if fast[i] > slow[i] * 1.0015:
                out[i] = Signal(ts=0, action="buy", strength=clamp((fast[i] / max(slow[i], 1e-12)) - 1.0, 0.0, 1.0), reason="ema_cross_up")
            elif fast[i] < slow[i] * 0.9985:
                out[i] = Signal(ts=0, action="sell", strength=clamp((slow[i] / max(fast[i], 1e-12)) - 1.0, 0.0, 1.0), reason="ema_cross_dn")
            else:
                out[i] = Signal(ts=0, action="hold", strength=0.1, reason="ema_flat")
        return out

    def _mean_revert(self, closes: list[float]) -> list[Signal | None]:
        rsi = Indicators.rsi(closes, self.cfg.rsi_window)
        z = Indicators.zscore(closes, self.cfg.z_window)
        out: list[Signal | None] = [None] * len(closes)
        for i in range(len(closes)):
            if rsi[i] is None or z[i] is None:
                continue
            if rsi[i] <= self.cfg.rsi_buy_below and z[i] <= -self.cfg.z_enter:
                strength = clamp((abs(z[i]) - self.cfg.z_enter) / max(3.0, self.cfg.z_enter), 0.0, 1.0)
                out[i] = Signal(ts=0, action="buy", strength=strength, reason="rsi_z_oversold")
            elif rsi[i] >= self.cfg.rsi_sell_above and z[i] >= self.cfg.z_enter:
                strength = clamp((abs(z[i]) - self.cfg.z_enter) / max(3.0, self.cfg.z_enter), 0.0, 1.0)
                out[i] = Signal(ts=0, action="sell", strength=strength, reason="rsi_z_overbought")
            else:
                # exit zones: small strength for de-risking
                if z[i] is not None and abs(z[i]) <= self.cfg.z_exit:
                    out[i] = Signal(ts=0, action="hold", strength=0.15, reason="z_neutral")
                else:
                    out[i] = Signal(ts=0, action="hold", strength=0.05, reason="mr_wait")
        return out

    def generate(self, candles: list[Candle]) -> list[Signal]:
        if len(candles) < max(self.cfg.ema_slow, self.cfg.z_window, self.cfg.rsi_window) + 5:
            raise StrategyError("not enough candles for indicators")
        closes = [c.close for c in candles]
        mom = self._momentum(closes)
        mr = self._mean_revert(closes)
        out: list[Signal] = []
        for i, c in enumerate(candles):
            a = mom[i]
            b = mr[i]
            if a is None or b is None:
                out.append(Signal(ts=c.ts, action="hold", strength=0.0, reason="warmup"))
                continue
            if self.cfg.mode == "momentum":
                out.append(dataclasses.replace(a, ts=c.ts))
                continue
            if self.cfg.mode == "mean_revert":
                out.append(dataclasses.replace(b, ts=c.ts))
                continue

            # blend: mean revert overrides on extreme z, otherwise momentum guides
            if b.action != "hold" and b.strength >= 0.25:
                out.append(dataclasses.replace(b, ts=c.ts, strength=clamp(0.55 + 0.45 * b.strength, 0.0, 1.0), reason=f"blend:{b.reason}"))
            else:
                # scale momentum by distance between EMAs
                out.append(dataclasses.replace(a, ts=c.ts, strength=clamp(0.35 + 0.65 * a.strength, 0.0, 1.0), reason=f"blend:{a.reason}"))
        return out


class ExecutionSim:
    """
    Simple execution + fee model:
    - A synthetic quote with fixed spread_bps.
    - Slippage proportional to order notional vs a liquidity proxy from volume.
    """

    def __init__(self, risk: RiskLimits, *, seed: int):
        self.risk = risk
        self.rng = random.Random(seed)

    def quote(self, candle: Candle) -> Quote:
        mid = candle.close
        spread = self.risk.spread_bps
        return Quote(ts=candle.ts, price=mid, spread_bps=spread)

    def _liquidity_proxy(self, candle: Candle) -> float:
        # Use dollar volume proxy: close * volume, with floor to avoid division blowups.
        return max(candle.close * max(candle.volume, 0.0), 1.0)

    def fill_price(self, candle: Candle, side: str, notional: float) -> float:
        q = self.quote(candle)
        half_spread = bps_to_frac(q.spread_bps) / 2.0
        spread_mult = (1.0 + half_spread) if side == "buy" else (1.0 - half_spread)
        # slippage: scaled by sqrt(notional/liquidity)
        liq = self._liquidity_proxy(candle)
        impact = math.sqrt(max(notional / liq, 0.0))
        impact = clamp(impact, 0.0, 0.25)
        slip = bps_to_frac(self.risk.slippage_bps) * (0.4 + 0.8 * impact)
        slip_mult = (1.0 + slip) if side == "buy" else (1.0 - slip)
        px = q.price * spread_mult * slip_mult
        # tiny jitter to avoid pathologies; deterministic via seed
        jitter = 1.0 + (self.rng.random() - 0.5) * 0.00015
        return px * jitter

    def fee(self, notional: float) -> float:
        return abs(notional) * bps_to_frac(self.risk.fee_bps)


class RiskManager:
    def __init__(self, risk: RiskLimits):
        self.risk = risk
        self.day_start_ts: int | None = None
        self.day_start_equity: float | None = None
        self.day_min_equity: float | None = None

    def reset_day(self, ts: int, equity: float) -> None:
        self.day_start_ts = ts
        self.day_start_equity = equity
        self.day_min_equity = equity

    def update_equity(self, equity: float) -> None:
        if self.day_min_equity is None:
            self.day_min_equity = equity
        else:
            self.day_min_equity = min(self.day_min_equity, equity)

    def check_daily_loss(self) -> tuple[bool, str]:
        if self.day_start_equity is None or self.day_min_equity is None:
            return True, "warmup"
        loss = self.day_start_equity - self.day_min_equity
        if loss > self.risk.max_daily_loss:
            return False, f"max_daily_loss_exceeded loss={money(loss)} limit={money(self.risk.max_daily_loss)}"
        return True, "ok"

    def check_order(self, notional: float) -> tuple[bool, str]:
        if abs(notional) > self.risk.max_order_notional:
            return False, f"max_order_notional {money(abs(notional))}>{money(self.risk.max_order_notional)}"
        return True, "ok"

    def check_position(self, pos_notional: float) -> tuple[bool, str]:
        if abs(pos_notional) > self.risk.max_pos_notional:
            return False, f"max_pos_notional {money(abs(pos_notional))}>{money(self.risk.max_pos_notional)}"
        return True, "ok"


@dataclasses.dataclass(frozen=True)
class Decision:
    ts: int
    action: str
    qty: float
    notional: float
    reason: str
    strength: float

    def as_json(self) -> JSON:
        return dataclasses.asdict(self)


class TradePlanner:
    def __init__(self, cfg: StrategyConfig, risk: RiskManager):
        self.cfg = cfg
        self.risk = risk

    def plan(self, candle: Candle, signal: Signal, portfolio: Portfolio, symbol: str) -> Decision:
        price = candle.close
        pos = portfolio.get_pos(symbol)
        pos_notional = pos.qty * price

        # rebalance logic: aim for +/- target_pos_notional depending on signal
        target = 0.0
        if signal.action == "buy":
            target = self.cfg.target_pos_notional * clamp(0.4 + 0.6 * signal.strength, 0.0, 1.0)
        elif signal.action == "sell":
            target = -self.cfg.target_pos_notional * clamp(0.4 + 0.6 * signal.strength, 0.0, 1.0)
        else:
            # drift toward flat if out of band
            if abs(pos_notional) > self.cfg.target_pos_notional * 0.85:
                target = math.copysign(self.cfg.target_pos_notional * 0.35, pos_notional)
            else:
                target = pos_notional

        delta = target - pos_notional
        band = abs(target) * bps_to_frac(self.cfg.rebalance_bps) + (10.0 if abs(target) < 50 else 0.0)
        if abs(delta) <= band:
            return Decision(ts=candle.ts, action="hold", qty=0.0, notional=0.0, reason=f"{signal.reason}:in_band", strength=signal.strength)

        notional = delta
        ok, why = self.risk.check_order(notional)
        if not ok:
            # clip toward limit
            cap = self.risk.risk.max_order_notional
            notional = math.copysign(cap, notional)
            ok2, _ = self.risk.check_order(notional)
            if not ok2:
                return Decision(ts=candle.ts, action="hold", qty=0.0, notional=0.0, reason=f"risk_block:{why}", strength=signal.strength)

        # ensure we do not exceed max position after fill (approx)
        next_pos_notional = pos_notional + notional
        okp, whyp = self.risk.check_position(next_pos_notional)
        if not okp:
            # reduce to fit
            cap = self.risk.risk.max_pos_notional
            notional = clamp(next_pos_notional, -cap, cap) - pos_notional
            if abs(notional) < 1.0:
                return Decision(ts=candle.ts, action="hold", qty=0.0, notional=0.0, reason=f"risk_pos_block:{whyp}", strength=signal.strength)

        qty = notional / max(price, 1e-12)
        if qty > 0:
            act = "buy"
        elif qty < 0:
            act = "sell"
        else:
            act = "hold"
        return Decision(ts=candle.ts, action=act, qty=abs(qty), notional=notional, reason=f"{signal.reason}:rebalance", strength=signal.strength)


class OrderManager:
    def __init__(self, store: SqliteStore, execsim: ExecutionSim, risk: RiskManager, *, symbol: str):
        self.store = store
        self.execsim = execsim
        self.risk = risk
        self.symbol = symbol

    def submit_market(self, ts: int, side: str, qty: float, *, client_tag: str) -> Order:
        oid = uuid.uuid4().hex
        order = Order(
            order_id=oid,
            symbol=self.symbol,
            side=side,
            qty=float(qty),
            limit_price=None,
            time_in_force="IOC",
            created_ts=int(ts),
            client_tag=client_tag,
        )
        self.store.insert_order(order)
        return order

    def try_fill(self, order: Order, candle: Candle) -> Fill:
        notional = order.qty * candle.close
        fee = self.execsim.fee(notional)
        px = self.execsim.fill_price(candle, order.side, abs(notional))
        fill = Fill(
            order_id=order.order_id,
            symbol=order.symbol,
            side=order.side,
            qty=order.qty,
            price=px,
            fee=fee,
            ts=candle.ts,
            liquidity="taker",
        )
        self.store.insert_fill(fill)
        self.store.update_order_fill(order.order_id, filled_qty=order.qty, avg_price=px, status="filled")
        return fill


@dataclasses.dataclass
class BacktestResult:
    run_id: str
    started_at: str
    ended_at: str
    candles: int
    fills: int
    start_cash: float
    end_cash: float
    end_equity: float
    fees_paid: float
    realized_pnl: float
    max_drawdown: float
    sharpe_like: float
    notes: str

    def as_json(self) -> JSON:
        return dataclasses.asdict(self)


def compute_drawdown(equity: list[tuple[int, float]]) -> float:
    peak = -1e99
    dd = 0.0
    for _, v in equity:
        peak = max(peak, v)
        dd = min(dd, v - peak)
    return dd


def sharpe_like(equity: list[tuple[int, float]]) -> float:
    if len(equity) < 5:
        return 0.0
    rets = []
    for i in range(1, len(equity)):
        prev = equity[i - 1][1]
        cur = equity[i][1]
        if prev <= 0:
            continue
        rets.append((cur - prev) / prev)
    if len(rets) < 10:
        return 0.0
    mu = statistics.fmean(rets)
    sd = statistics.pstdev(rets) or 1e-12
    return mu / sd * math.sqrt(365.0)


class Backtester:
    def __init__(self, cfg: AppConfig, store: SqliteStore, *, log: logging.Logger):
        self.cfg = cfg
        self.store = store
        self.log = log
        self.rng = random.Random(cfg.seed)
        self.execsim = ExecutionSim(cfg.risk, seed=cfg.seed ^ 0x5A17C3)
        self.riskm = RiskManager(cfg.risk)
        self.strategy = BlendStrategy(cfg.strat)
        self.planner = TradePlanner(cfg.strat, self.riskm)
        self.orderm = OrderManager(store, self.execsim, self.riskm, symbol=cfg.symbol)

    def run(self, candles: list[Candle], *, start_cash: float) -> tuple[BacktestResult, Portfolio, list[Decision]]:
        run_id = uuid.uuid4().hex
        portfolio = Portfolio(cash=float(start_cash))
        signals = self.strategy.generate(candles)
        decisions: list[Decision] = []
        fills = 0

        if candles:
            self.riskm.reset_day(candles[0].ts, start_cash)

        for i, c in enumerate(candles):
            # reset daily counters at UTC day boundary
            if i > 0:
                prev = _dt.datetime.fromtimestamp(candles[i - 1].ts, tz=_dt.timezone.utc).date()
                cur = _dt.datetime.fromtimestamp(c.ts, tz=_dt.timezone.utc).date()
                if cur != prev:
                    eq_prev = portfolio.equity_curve[-1][1] if portfolio.equity_curve else start_cash
                    self.riskm.reset_day(c.ts, eq_prev)

            px = c.close
            equity = portfolio.mark_to_market(c.ts, {self.cfg.symbol: px})
            self.riskm.update_equity(equity)
            ok_loss, why_loss = self.riskm.check_daily_loss()
            if not ok_loss:
                decisions.append(Decision(ts=c.ts, action="hold", qty=0.0, notional=0.0, reason=f"risk:{why_loss}", strength=0.0))
                continue

            s = signals[i]
            d = self.planner.plan(c, s, portfolio, self.cfg.symbol)
            decisions.append(d)
            if d.action == "hold" or d.qty <= 0:
                continue

            order = self.orderm.submit_market(c.ts, d.action, d.qty, client_tag=f"bt:{run_id[:10]}:{d.reason}")
            fill = self.orderm.try_fill(order, c)
            portfolio.apply_fill(fill)
            fills += 1

        end_equity = portfolio.equity_curve[-1][1] if portfolio.equity_curve else start_cash
        dd = compute_drawdown(portfolio.equity_curve)
        sh = sharpe_like(portfolio.equity_curve)
        realized = sum(p.realized_pnl for p in portfolio.positions.values())
        started_at = iso(_dt.datetime.fromtimestamp(candles[0].ts, tz=_dt.timezone.utc)) if candles else iso()
        ended_at = iso(_dt.datetime.fromtimestamp(candles[-1].ts, tz=_dt.timezone.utc)) if candles else iso()

        res = BacktestResult(
            run_id=run_id,
            started_at=started_at,
            ended_at=ended_at,
            candles=len(candles),
            fills=fills,
            start_cash=float(start_cash),
            end_cash=float(portfolio.cash),
            end_equity=float(end_equity),
            fees_paid=float(portfolio.fees_paid),
            realized_pnl=float(realized),
            max_drawdown=float(dd),
            sharpe_like=float(sh),
            notes="paper backtest; includes spread+slippage+fee model",
        )
        return res, portfolio, decisions


class EventBus:
    def __init__(self):
        self._q: "queue.Queue[JSON]" = queue.Queue(maxsize=10_000)

    def publish(self, event: JSON) -> None:
        try:
            self._q.put_nowait(event)
        except queue.Full:
            # drop if overloaded; UI is best-effort
            pass

    def drain(self, *, limit: int = 250) -> list[JSON]:
        out: list[JSON] = []
        for _ in range(limit):
            try:
                out.append(self._q.get_nowait())
            except queue.Empty:
                break
        return out


class BotState:
    def __init__(self, cfg: AppConfig, store: SqliteStore, *, log: logging.Logger):
        self.cfg = cfg
        self.store = store
        self.log = log
        self.bus = EventBus()
        self._lock = threading.Lock()

        self.candles: list[Candle] = []
        self.last_backtest: BacktestResult | None = None
        self.last_portfolio: Portfolio | None = None
        self.last_decisions: list[Decision] = []
        self._status: str = "idle"
        self._status_detail: str = ""
        self._last_error: str | None = None

    def set_status(self, status: str, detail: str = "") -> None:
        with self._lock:
            self._status = status
            self._status_detail = detail
        self.bus.publish({"t": "status", "status": status, "detail": detail, "at": iso()})

    def set_error(self, msg: str) -> None:
        with self._lock:
            self._last_error = msg
        self.bus.publish({"t": "error", "message": msg, "at": iso()})

    def snapshot(self) -> JSON:
        with self._lock:
            return {
                "app": self.cfg.appname,
                "instance_id": self.cfg.instance_id,
                "status": self._status,
                "detail": self._status_detail,
                "last_error": self._last_error,
                "candles_loaded": len(self.candles),
                "last_backtest": None if self.last_backtest is None else self.last_backtest.as_json(),
            }


def read_json_body(rfile: io.BufferedReader, content_length: int) -> JSON:
    data = rfile.read(content_length) if content_length > 0 else b"{}"
    try:
        obj = json.loads(data.decode("utf-8"))
    except json.JSONDecodeError as e:
        raise MeowsterError(f"invalid JSON: {e}") from e
    if not isinstance(obj, dict):
        raise MeowsterError("JSON body must be an object")
    return t.cast(JSON, obj)


def json_response(handler: http.server.BaseHTTPRequestHandler, status: int, payload: JSON, *, headers: dict[str, str] | None = None) -> None:
    body = json.dumps(payload, ensure_ascii=False, separators=(",", ":"), sort_keys=True).encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", "application/json; charset=utf-8")
    handler.send_header("Content-Length", str(len(body)))
    handler.send_header("Cache-Control", "no-store")
    handler.send_header("Access-Control-Allow-Origin", "*")
    handler.send_header("Access-Control-Allow-Headers", "Content-Type, X-Meowster-Token")
    handler.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
    if headers:
        for k, v in headers.items():
            handler.send_header(k, v)
    handler.end_headers()
    handler.wfile.write(body)


def text_response(handler: http.server.BaseHTTPRequestHandler, status: int, text: str, *, ctype: str = "text/plain; charset=utf-8") -> None:
    body = text.encode("utf-8")
    handler.send_response(status)
    handler.send_header("Content-Type", ctype)
    handler.send_header("Content-Length", str(len(body)))
    handler.send_header("Cache-Control", "no-store")
    handler.send_header("Access-Control-Allow-Origin", "*")
    handler.send_header("Access-Control-Allow-Headers", "Content-Type, X-Meowster-Token")
    handler.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
    handler.end_headers()
    handler.wfile.write(body)


def parse_query(path: str) -> tuple[str, dict[str, str]]:
    u = urllib.parse.urlparse(path)
    q = urllib.parse.parse_qs(u.query)
    flat = {k: (v[0] if v else "") for k, v in q.items()}
    return u.path, flat


class TokenAuth:
    def __init__(self, secret: str):
        self.secret = secret.encode("utf-8")

    def mint(self, subject: str, *, ttl_s: int = 3600) -> str:
        exp = int(time.time()) + int(ttl_s)
        nonce = uuid.uuid4().hex[:12]
        msg = f"{subject}|{exp}|{nonce}".encode("utf-8")
        sig = hmac.new(self.secret, msg, hashlib.sha256).digest()
        tok = base64.urlsafe_b64encode(msg + b"." + sig).decode("ascii").rstrip("=")
        return tok

    def verify(self, token: str) -> tuple[bool, str]:
        try:
            pad = "=" * (-len(token) % 4)
            raw = base64.urlsafe_b64decode((token + pad).encode("ascii"))
            msg, sig = raw.rsplit(b".", 1)
            expect = hmac.new(self.secret, msg, hashlib.sha256).digest()
            if not hmac.compare_digest(sig, expect):
                return False, "bad_sig"
            parts = msg.decode("utf-8").split("|")
            if len(parts) != 3:
                return False, "bad_fmt"
            exp = int(parts[1])
            if time.time() > exp:
                return False, "expired"
            return True, parts[0]
        except Exception:
            return False, "error"


class ApiHandler(http.server.BaseHTTPRequestHandler):
    server_version = "meowster/1.0"

    def log_message(self, fmt: str, *args: t.Any) -> None:
        self.server.log.info("%s - %s", self.address_string(), fmt % args)

    @property
    def server(self) -> "MeowsterServer":  # type: ignore[override]
        return t.cast("MeowsterServer", super().server)

    def do_OPTIONS(self) -> None:  # noqa: N802
        self.send_response(204)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Headers", "Content-Type, X-Meowster-Token")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.end_headers()

    def _require_token(self) -> tuple[bool, str]:
        if not self.server.require_token:
            return True, "disabled"
        tok = self.headers.get("X-Meowster-Token", "").strip()
        if not tok:
            return False, "missing"
        ok, sub = self.server.auth.verify(tok)
        return ok, sub

    def do_GET(self) -> None:  # noqa: N802
        path, q = parse_query(self.path)
        try:
            if path == "/":
                text_response(self, 200, "meowster is running\n")
                return
            if path == "/api/ping":
                json_response(self, 200, {"ok": True, "ts": int(time.time()), "iso": iso()})
                return
            if path == "/api/config":
                json_response(self, 200, {"ok": True, "config": self.server.state.cfg.as_json()})
                return
            if path == "/api/state":
                json_response(self, 200, {"ok": True, "state": self.server.state.snapshot()})
                return
            if path == "/api/events":
                ev = self.server.state.bus.drain(limit=parse_int(q.get("limit", ""), default=250) or 250)
                json_response(self, 200, {"ok": True, "events": ev})
                return
            if path == "/api/orders":
                ok, _ = self._require_token()
                if not ok:
                    json_response(self, 401, {"ok": False, "error": "unauthorized"})
                    return
                lim = parse_int(q.get("limit", ""), default=200) or 200
                json_response(self, 200, {"ok": True, "orders": self.server.store.list_orders(limit=lim)})
                return
            if path == "/api/fills":
                ok, _ = self._require_token()
                if not ok:
                    json_response(self, 401, {"ok": False, "error": "unauthorized"})
                    return
                lim = parse_int(q.get("limit", ""), default=500) or 500
                json_response(self, 200, {"ok": True, "fills": self.server.store.list_fills(limit=lim)})
                return
            if path == "/api/equity":
                ok, _ = self._require_token()
                if not ok:
                    json_response(self, 401, {"ok": False, "error": "unauthorized"})
                    return
                snap = self.server.state.last_portfolio
                if snap is None:
                    json_response(self, 200, {"ok": True, "equity": []})
                    return
                eq = [{"ts": ts, "equity": v} for ts, v in snap.equity_curve[-2000:]]
                json_response(self, 200, {"ok": True, "equity": eq})
                return
            if path == "/api/decisions":
                ok, _ = self._require_token()
                if not ok:
                    json_response(self, 401, {"ok": False, "error": "unauthorized"})
                    return
                d = [x.as_json() for x in self.server.state.last_decisions[-1000:]]
                json_response(self, 200, {"ok": True, "decisions": d})
                return
            json_response(self, 404, {"ok": False, "error": "not_found", "path": path})
        except Exception as e:
            self.server.state.set_error(f"GET {path} failed: {e}")
            json_response(self, 500, {"ok": False, "error": "server_error"})

    def do_POST(self) -> None:  # noqa: N802
        path, q = parse_query(self.path)
        try:
            if path == "/api/auth/mint":
                # Optional token auth mint endpoint; if token auth disabled, still returns a token for UI parity.
                length = int(self.headers.get("Content-Length", "0") or "0")
                body = read_json_body(self.rfile, length)
                subject = str(body.get("subject") or "kasha")
                ttl = int(body.get("ttl_s") or 3600)
                tok = self.server.auth.mint(subject, ttl_s=ttl)
                json_response(self, 200, {"ok": True, "token": tok, "subject": subject, "ttl_s": ttl})
                return
