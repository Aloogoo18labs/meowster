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
