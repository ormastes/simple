"""pykrx data source — Tier 1 (free, no API key required).

Wraps pykrx.stock for OHLCV, market cap, ticker lists, and index data.
"""

from __future__ import annotations

import pandas as pd
from pykrx import stock as krx

from korean_stock_mcp.utils.cache import cache, TTLCache
from korean_stock_mcp.utils.formatting import today_yyyymmdd, days_ago_yyyymmdd, to_yyyymmdd
from korean_stock_mcp.utils.rate_limiter import api_limiter


def get_ticker_list(market: str = "ALL") -> list[dict[str, str]]:
    """Get list of all tickers for a market.

    Args:
        market: "KOSPI", "KOSDAQ", or "ALL"
    """
    cache_key = f"ticker_list:{market}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    date = today_yyyymmdd()

    result = []
    markets = ["KOSPI", "KOSDAQ"] if market == "ALL" else [market.upper()]
    for mkt in markets:
        tickers = krx.get_market_ticker_list(date, market=mkt)
        for ticker in tickers:
            name = krx.get_market_ticker_name(ticker)
            result.append({"ticker": ticker, "name": name, "market": mkt})

    cache.set(cache_key, result, TTLCache.LIST_TTL)
    return result


def search_ticker(query: str) -> list[dict[str, str]]:
    """Search for tickers by name (Korean or partial match)."""
    all_tickers = get_ticker_list("ALL")
    query_lower = query.lower()
    return [
        t for t in all_tickers
        if query_lower in t["name"].lower() or query_lower in t["ticker"]
    ]


def get_ohlcv(ticker: str, start: str | None = None, end: str | None = None) -> list[dict]:
    """Get OHLCV data for a ticker.

    Args:
        ticker: 6-digit ticker code (e.g., "005930")
        start: Start date (YYYY-MM-DD or YYYYMMDD). Defaults to 30 days ago.
        end: End date. Defaults to today.
    """
    end_date = to_yyyymmdd(end) if end else today_yyyymmdd()
    start_date = to_yyyymmdd(start) if start else days_ago_yyyymmdd(30)

    cache_key = f"ohlcv:{ticker}:{start_date}:{end_date}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    df = krx.get_market_ohlcv_by_date(start_date, end_date, ticker)

    if df.empty:
        return []

    result = []
    for date_idx, row in df.iterrows():
        result.append({
            "date": date_idx.strftime("%Y-%m-%d"),
            "open": int(row["시가"]),
            "high": int(row["고가"]),
            "low": int(row["저가"]),
            "close": int(row["종가"]),
            "volume": int(row["거래량"]),
        })

    cache.set(cache_key, result, cache.get_price_ttl())
    return result


def get_current_price(ticker: str) -> dict | None:
    """Get the latest price data for a ticker."""
    data = get_ohlcv(ticker, start=days_ago_yyyymmdd(7))
    if not data:
        return None
    latest = data[-1]
    if len(data) >= 2:
        prev_close = data[-2]["close"]
        change = latest["close"] - prev_close
        change_pct = (change / prev_close) * 100 if prev_close else 0
        latest["change"] = change
        latest["change_pct"] = round(change_pct, 2)
    return latest


def get_market_cap(ticker: str) -> dict | None:
    """Get market cap data for a ticker."""
    date = today_yyyymmdd()
    cache_key = f"mcap:{ticker}:{date}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    df = krx.get_market_cap_by_date(days_ago_yyyymmdd(7), date, ticker)
    if df.empty:
        return None

    row = df.iloc[-1]
    result = {
        "date": df.index[-1].strftime("%Y-%m-%d"),
        "market_cap": int(row["시가총액"]),
        "shares_outstanding": int(row["상장주식수"]),
        "volume": int(row["거래량"]),
    }
    cache.set(cache_key, result, cache.get_price_ttl())
    return result


def get_market_index(index_name: str = "코스피") -> dict | None:
    """Get market index data.

    Args:
        index_name: "코스피" (KOSPI) or "코스닥" (KOSDAQ)
    """
    date = today_yyyymmdd()
    cache_key = f"index:{index_name}:{date}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    # Map English names to Korean
    name_map = {
        "kospi": "코스피",
        "kosdaq": "코스닥",
    }
    kr_name = name_map.get(index_name.lower(), index_name)

    df = krx.get_index_ohlcv_by_date(days_ago_yyyymmdd(7), date, "1001" if kr_name == "코스피" else "2001")
    if df.empty:
        return None

    row = df.iloc[-1]
    result = {
        "date": df.index[-1].strftime("%Y-%m-%d"),
        "name": kr_name,
        "close": float(row["종가"]),
        "volume": int(row["거래량"]),
    }
    if len(df) >= 2:
        prev = float(df.iloc[-2]["종가"])
        result["change"] = round(float(row["종가"]) - prev, 2)
        result["change_pct"] = round(((float(row["종가"]) - prev) / prev) * 100, 2)

    cache.set(cache_key, result, cache.get_price_ttl())
    return result


def get_sector_data(date: str | None = None) -> list[dict]:
    """Get sector-level performance data."""
    target_date = to_yyyymmdd(date) if date else today_yyyymmdd()
    cache_key = f"sector:{target_date}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    api_limiter.acquire()
    df = krx.get_index_portfolio_deposit_file("1001", target_date)
    if isinstance(df, pd.DataFrame) and not df.empty:
        result = df.to_dict("records")
    else:
        result = []

    cache.set(cache_key, result, TTLCache.PRICE_TTL_CLOSED)
    return result
