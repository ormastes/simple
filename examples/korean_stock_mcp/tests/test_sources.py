"""Tests for data source adapters."""

from __future__ import annotations

from unittest.mock import patch, MagicMock

import pandas as pd
import pytest

from korean_stock_mcp.utils.cache import TTLCache
from korean_stock_mcp.utils.formatting import format_krw, format_pct, to_yyyymmdd


class TestFormatting:
    """Test formatting utilities."""

    def test_format_krw_large(self):
        assert format_krw(1_5000_0000_0000) == "15,000.0억원"

    def test_format_krw_medium(self):
        assert format_krw(50000) == "5만원"

    def test_format_krw_small(self):
        assert format_krw(3500) == "3,500원"

    def test_format_pct_positive(self):
        assert format_pct(2.5) == "+2.50%"

    def test_format_pct_negative(self):
        assert format_pct(-1.3) == "-1.30%"

    def test_to_yyyymmdd_iso(self):
        assert to_yyyymmdd("2024-03-15") == "20240315"

    def test_to_yyyymmdd_already(self):
        assert to_yyyymmdd("20240315") == "20240315"


class TestCache:
    """Test TTL cache."""

    def test_set_get(self):
        c = TTLCache(default_ttl=60)
        c.set("key1", "value1")
        assert c.get("key1") == "value1"

    def test_expired(self):
        c = TTLCache(default_ttl=0)
        c.set("key1", "value1", ttl=0)
        # TTL=0 means instant expiry
        import time
        time.sleep(0.01)
        assert c.get("key1") is None

    def test_invalidate(self):
        c = TTLCache()
        c.set("key1", "value1")
        c.invalidate("key1")
        assert c.get("key1") is None

    def test_clear(self):
        c = TTLCache()
        c.set("a", 1)
        c.set("b", 2)
        c.clear()
        assert c.get("a") is None
        assert c.get("b") is None


class TestPykrxSource:
    """Test pykrx source adapter with mocked pykrx calls."""

    @patch("korean_stock_mcp.sources.pykrx_source.krx")
    def test_search_ticker(self, mock_krx, sample_ticker_list):
        mock_krx.get_market_ticker_list.return_value = ["005930", "000660"]
        mock_krx.get_market_ticker_name.side_effect = lambda t: {
            "005930": "삼성전자", "000660": "SK하이닉스"
        }.get(t, "")

        from korean_stock_mcp.sources.pykrx_source import search_ticker
        from korean_stock_mcp.utils.cache import cache
        cache.clear()

        results = search_ticker("삼성")
        assert any("삼성" in r["name"] for r in results)

    @patch("korean_stock_mcp.sources.pykrx_source.krx")
    def test_get_ohlcv(self, mock_krx):
        df = pd.DataFrame(
            {
                "시가": [73000],
                "고가": [73500],
                "저가": [72500],
                "종가": [73200],
                "거래량": [12345678],
            },
            index=pd.to_datetime(["2024-01-15"]),
        )
        mock_krx.get_market_ohlcv_by_date.return_value = df

        from korean_stock_mcp.sources.pykrx_source import get_ohlcv
        from korean_stock_mcp.utils.cache import cache
        cache.clear()

        result = get_ohlcv("005930", "2024-01-15", "2024-01-15")
        assert len(result) == 1
        assert result[0]["close"] == 73200
        assert result[0]["volume"] == 12345678
