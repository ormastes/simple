"""FinanceDataReader source — Tier 1 (free, no API key required).

Supplementary data source for broader coverage and alternative data.
"""

from __future__ import annotations

from datetime import datetime, timedelta

import FinanceDataReader as fdr

from korean_stock_mcp.utils.cache import cache, TTLCache
from korean_stock_mcp.utils.rate_limiter import api_limiter


def get_stock_listing(market: str = "KOSPI") -> list[dict[str, str]]:
    """Get stock listing from FinanceDataReader.

    Args:
        market: "KOSPI", "KOSDAQ", "KONEX"
    """
    cache_key = f"fdr_listing:{market}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    df = fdr.StockListing(market)
    result = []
    for _, row in df.iterrows():
        result.append({
            "ticker": str(row.get("Code", row.get("Symbol", ""))),
            "name": str(row.get("Name", "")),
            "market": market,
        })

    cache.set(cache_key, result, TTLCache.LIST_TTL)
    return result


def get_ohlcv(ticker: str, start: str | None = None, end: str | None = None) -> list[dict]:
    """Get OHLCV data via FinanceDataReader.

    Args:
        ticker: Ticker symbol (e.g., "005930" for Samsung)
        start: Start date (YYYY-MM-DD). Defaults to 30 days ago.
        end: End date. Defaults to today.
    """
    end_date = end or datetime.now().strftime("%Y-%m-%d")
    start_date = start or (datetime.now() - timedelta(days=30)).strftime("%Y-%m-%d")

    cache_key = f"fdr_ohlcv:{ticker}:{start_date}:{end_date}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    df = fdr.DataReader(ticker, start_date, end_date)
    if df.empty:
        return []

    result = []
    for date_idx, row in df.iterrows():
        result.append({
            "date": date_idx.strftime("%Y-%m-%d"),
            "open": int(row["Open"]),
            "high": int(row["High"]),
            "low": int(row["Low"]),
            "close": int(row["Close"]),
            "volume": int(row["Volume"]),
        })

    cache.set(cache_key, result, 300)
    return result


def get_index(index: str = "KS11", start: str | None = None) -> list[dict]:
    """Get market index data.

    Args:
        index: Index code — "KS11" (KOSPI), "KQ11" (KOSDAQ)
        start: Start date. Defaults to 30 days ago.
    """
    start_date = start or (datetime.now() - timedelta(days=30)).strftime("%Y-%m-%d")
    cache_key = f"fdr_index:{index}:{start_date}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    df = fdr.DataReader(index, start_date)
    if df.empty:
        return []

    result = []
    for date_idx, row in df.iterrows():
        result.append({
            "date": date_idx.strftime("%Y-%m-%d"),
            "close": float(row["Close"]),
            "volume": int(row.get("Volume", 0)),
        })

    cache.set(cache_key, result, 300)
    return result
