"""Price-related MCP tools."""

from __future__ import annotations

from mcp.server.fastmcp import FastMCP

from korean_stock_mcp.sources import pykrx_source, fdr_source
from korean_stock_mcp.utils.formatting import format_krw, format_pct, format_volume


def register(mcp: FastMCP) -> None:
    """Register price tools with the MCP server."""

    @mcp.tool()
    def stock_price(ticker_or_name: str) -> str:
        """Get the current/latest stock price.

        Args:
            ticker_or_name: 6-digit ticker (e.g., "005930") or Korean company name (e.g., "삼성전자")
        """
        # Resolve name to ticker if needed
        ticker = ticker_or_name
        if not ticker_or_name.isdigit():
            matches = pykrx_source.search_ticker(ticker_or_name)
            if not matches:
                return f"No stock found matching '{ticker_or_name}'"
            ticker = matches[0]["ticker"]
            name = matches[0]["name"]
        else:
            matches = pykrx_source.search_ticker(ticker_or_name)
            name = matches[0]["name"] if matches else ticker

        data = pykrx_source.get_current_price(ticker)
        if not data:
            return f"No price data available for {ticker}"

        lines = [
            f"**{name}** ({ticker})",
            f"Price: {format_krw(data['close'])}",
            f"Open: {format_krw(data['open'])} | High: {format_krw(data['high'])} | Low: {format_krw(data['low'])}",
            f"Volume: {format_volume(data['volume'])}",
            f"Date: {data['date']}",
        ]
        if "change" in data:
            lines.append(f"Change: {format_krw(data['change'])} ({format_pct(data['change_pct'])})")
        return "\n".join(lines)

    @mcp.tool()
    def stock_ohlcv(ticker: str, start: str | None = None, end: str | None = None) -> str:
        """Get historical OHLCV (Open/High/Low/Close/Volume) data.

        Args:
            ticker: 6-digit stock ticker (e.g., "005930")
            start: Start date (YYYY-MM-DD). Defaults to 30 days ago.
            end: End date (YYYY-MM-DD). Defaults to today.
        """
        data = pykrx_source.get_ohlcv(ticker, start, end)
        if not data:
            return f"No OHLCV data for {ticker}"

        lines = [f"OHLCV for {ticker} ({len(data)} days)", ""]
        lines.append("| Date | Open | High | Low | Close | Volume |")
        lines.append("|------|------|------|-----|-------|--------|")
        for row in data[-20:]:  # Last 20 entries max
            lines.append(
                f"| {row['date']} | {row['open']:,} | {row['high']:,} | "
                f"{row['low']:,} | {row['close']:,} | {row['volume']:,} |"
            )
        if len(data) > 20:
            lines.append(f"\n(Showing last 20 of {len(data)} records)")
        return "\n".join(lines)
