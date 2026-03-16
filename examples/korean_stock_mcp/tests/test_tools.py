"""Tests for MCP tool registration and server startup."""

from __future__ import annotations

import json
import subprocess
import sys


def test_server_imports():
    """Verify that the server module can be imported without errors."""
    result = subprocess.run(
        [sys.executable, "-c", "from korean_stock_mcp.server import mcp; print('OK')"],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, f"Import failed: {result.stderr}"
    assert "OK" in result.stdout


def test_tools_registered():
    """Verify all expected tools are registered."""
    result = subprocess.run(
        [
            sys.executable,
            "-c",
            "from korean_stock_mcp.server import mcp; "
            "tools = mcp._tool_manager._tools; "
            "print(','.join(sorted(tools.keys())))",
        ],
        capture_output=True,
        text=True,
        timeout=30,
    )
    assert result.returncode == 0, f"Failed: {result.stderr}"

    registered = set(result.stdout.strip().split(","))
    expected = {
        "stock_price",
        "stock_ohlcv",
        "stock_search",
        "stock_list",
        "market_index",
        "market_cap",
        "company_info",
        "financial_statements",
        "market_news",
        "stock_news",
        "sector_performance",
        "stock_compare",
    }
    missing = expected - registered
    assert not missing, f"Missing tools: {missing}"
