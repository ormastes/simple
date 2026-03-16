"""DART (Data Analysis, Retrieval and Transfer) source — Tier 2.

Requires free API key from https://opendart.fss.or.kr
Provides company disclosures and financial statements.
"""

from __future__ import annotations

import httpx

from korean_stock_mcp.utils.cache import cache, TTLCache
from korean_stock_mcp.utils.config import get_dart_api_key
from korean_stock_mcp.utils.rate_limiter import api_limiter

DART_BASE_URL = "https://opendart.fss.or.kr/api"


def _is_available() -> bool:
    """Check if DART API key is configured."""
    return get_dart_api_key() is not None


def _get(endpoint: str, params: dict | None = None) -> dict | None:
    """Make a DART API request."""
    api_key = get_dart_api_key()
    if not api_key:
        return None

    api_limiter.acquire()
    all_params = {"crtfc_key": api_key}
    if params:
        all_params.update(params)

    with httpx.Client(timeout=30) as client:
        resp = client.get(f"{DART_BASE_URL}/{endpoint}.json", params=all_params)
        resp.raise_for_status()
        data = resp.json()

    if data.get("status") != "000":
        return None
    return data


def get_corp_code(ticker: str) -> str | None:
    """Look up DART corporation code from stock ticker.

    DART uses its own corp_code, not the stock ticker.
    """
    cache_key = f"dart_corp:{ticker}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    # DART corp code lookup requires downloading the full XML
    # For simplicity, we use the company search endpoint
    data = _get("company", {"corp_code": ticker})
    if data and data.get("corp_code"):
        cache.set(cache_key, data["corp_code"], TTLCache.LIST_TTL)
        return data["corp_code"]
    return None


def get_company_info(corp_code: str) -> dict | None:
    """Get company overview from DART.

    Args:
        corp_code: DART corporation code or stock ticker
    """
    if not _is_available():
        return None

    cache_key = f"dart_company:{corp_code}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    data = _get("company", {"corp_code": corp_code})
    if not data:
        return None

    result = {
        "corp_name": data.get("corp_name", ""),
        "corp_name_eng": data.get("corp_name_eng", ""),
        "stock_code": data.get("stock_code", ""),
        "ceo_name": data.get("ceo_nm", ""),
        "corp_class": data.get("corp_cls", ""),
        "industry": data.get("induty_code", ""),
        "establishment_date": data.get("est_dt", ""),
        "homepage": data.get("hm_url", ""),
        "address": data.get("adres", ""),
    }
    cache.set(cache_key, result, TTLCache.LIST_TTL)
    return result


def get_financial_statements(
    corp_code: str,
    year: str,
    report_code: str = "11011",
) -> list[dict] | None:
    """Get financial statements from DART.

    Args:
        corp_code: DART corporation code
        year: Business year (e.g., "2024")
        report_code: "11011" (annual), "11012" (semi-annual),
                     "11013" (Q1), "11014" (Q3)
    """
    if not _is_available():
        return None

    cache_key = f"dart_fin:{corp_code}:{year}:{report_code}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached

    data = _get("fnlttSinglAcnt", {
        "corp_code": corp_code,
        "bsns_year": year,
        "reprt_code": report_code,
        "fs_div": "OFS",  # Individual financial statements
    })
    if not data or "list" not in data:
        return None

    result = []
    for item in data["list"]:
        result.append({
            "account_name": item.get("account_nm", ""),
            "current_amount": item.get("thstrm_amount", ""),
            "previous_amount": item.get("frmtrm_amount", ""),
            "before_previous": item.get("bfefrmtrm_amount", ""),
        })

    cache.set(cache_key, result, TTLCache.LIST_TTL)
    return result
