"""KRX Open API source — Tier 2.

Requires free API key from https://open.krx.co.kr
Provides official exchange data.
"""

from __future__ import annotations

import httpx

from korean_stock_mcp.utils.cache import cache, TTLCache
from korean_stock_mcp.utils.config import get_krx_api_key
from korean_stock_mcp.utils.rate_limiter import api_limiter

KRX_BASE_URL = "http://data-dbg.krx.co.kr/svc/apis"


def _is_available() -> bool:
    """Check if KRX API key is configured."""
    return get_krx_api_key() is not None


def _get(endpoint: str, params: dict | None = None) -> dict | None:
    """Make a KRX API request."""
    api_key = get_krx_api_key()
    if not api_key:
        return None

    api_limiter.acquire()
    headers = {"AUTH_KEY": api_key}
    all_params = params or {}

    with httpx.Client(timeout=30) as client:
        resp = client.get(
            f"{KRX_BASE_URL}/{endpoint}",
            params=all_params,
            headers=headers,
        )
        resp.raise_for_status()
        return resp.json()


def get_market_data(ticker: str) -> dict | None:
    """Get real-time market data from KRX.

    Args:
        ticker: 6-digit stock ticker
    """
    if not _is_available():
        return None

    cache_key = f"krx_market:{ticker}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    data = _get("sto/stk_bydd_trd", {"isuCd": ticker})
    if not data or "OutBlock_1" not in data:
        return None

    items = data["OutBlock_1"]
    if not items:
        return None

    latest = items[-1] if isinstance(items, list) else items
    result = {
        "ticker": ticker,
        "close": latest.get("TDD_CLSPRC", ""),
        "volume": latest.get("ACC_TRDVOL", ""),
        "trade_value": latest.get("ACC_TRDVAL", ""),
    }
    cache.set(cache_key, result, TTLCache.PRICE_TTL)
    return result
