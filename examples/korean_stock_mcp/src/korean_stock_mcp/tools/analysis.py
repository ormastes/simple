"""Analysis MCP tools — sector performance and stock comparison."""

from __future__ import annotations

from mcp.server.fastmcp import FastMCP

from korean_stock_mcp.sources import pykrx_source
from korean_stock_mcp.utils.formatting import format_krw, format_pct, format_volume


def register(mcp: FastMCP) -> None:
    """Register analysis tools with the MCP server."""

    @mcp.tool()
    def sector_performance(date: str | None = None) -> str:
        """Get sector-level performance data for the Korean market.

        Args:
            date: Target date (YYYY-MM-DD). Defaults to today/latest trading day.
        """
        data = pykrx_source.get_sector_data(date)
        if not data:
            return "No sector data available. This may happen on holidays or weekends."

        lines = ["Korean Market Sector Performance", ""]
        lines.append("| Sector | Value |")
        lines.append("|--------|-------|")
        for item in data[:30]:
            lines.append(f"| {item} |")
        return "\n".join(lines)

    @mcp.tool()
    def stock_compare(tickers: str) -> str:
        """Compare multiple Korean stocks side by side.

        Args:
            tickers: Comma-separated list of 6-digit tickers (e.g., "005930,000660,035420")
        """
        ticker_list = [t.strip() for t in tickers.split(",") if t.strip()]
        if not ticker_list:
            return "Please provide at least one ticker"
        if len(ticker_list) > 10:
            return "Maximum 10 tickers for comparison"

        lines = ["Stock Comparison", ""]
        lines.append("| Ticker | Name | Price | Change | Volume | Market Cap |")
        lines.append("|--------|------|-------|--------|--------|------------|")

        for ticker in ticker_list:
            # Get name
            matches = pykrx_source.search_ticker(ticker)
            name = matches[0]["name"] if matches else ticker

            # Get price
            price_data = pykrx_source.get_current_price(ticker)
            mcap_data = pykrx_source.get_market_cap(ticker)

            if price_data:
                price_str = format_krw(price_data["close"])
                change_str = format_pct(price_data.get("change_pct", 0)) if "change_pct" in price_data else "N/A"
                vol_str = format_volume(price_data["volume"])
            else:
                price_str = change_str = vol_str = "N/A"

            mcap_str = format_krw(mcap_data["market_cap"]) if mcap_data else "N/A"

            lines.append(f"| {ticker} | {name} | {price_str} | {change_str} | {vol_str} | {mcap_str} |")

        return "\n".join(lines)
