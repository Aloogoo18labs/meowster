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
