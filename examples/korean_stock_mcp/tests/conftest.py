"""Test fixtures for Korean Stock MCP server tests."""

from __future__ import annotations

import pytest


@pytest.fixture
def sample_ohlcv():
    """Sample OHLCV data for testing."""
    return [
        {
            "date": "2024-01-15",
            "open": 73000,
            "high": 73500,
            "low": 72500,
            "close": 73200,
            "volume": 12345678,
        },
        {
            "date": "2024-01-16",
            "open": 73200,
            "high": 74000,
            "low": 73000,
            "close": 73800,
            "volume": 15678901,
        },
    ]


@pytest.fixture
def sample_ticker_list():
    """Sample ticker list for testing."""
    return [
        {"ticker": "005930", "name": "삼성전자", "market": "KOSPI"},
        {"ticker": "000660", "name": "SK하이닉스", "market": "KOSPI"},
        {"ticker": "035420", "name": "NAVER", "market": "KOSPI"},
        {"ticker": "035720", "name": "카카오", "market": "KOSPI"},
        {"ticker": "247540", "name": "에코프로비엠", "market": "KOSDAQ"},
    ]
