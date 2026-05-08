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
