"""Market index and cap MCP tools."""

from __future__ import annotations

from mcp.server.fastmcp import FastMCP

from korean_stock_mcp.sources import pykrx_source
from korean_stock_mcp.utils.formatting import format_krw, format_pct, format_volume


def register(mcp: FastMCP) -> None:
    """Register market tools with the MCP server."""

    @mcp.tool()
    def market_index(index_name: str = "KOSPI") -> str:
        """Get Korean market index data.

        Args:
            index_name: "KOSPI" or "KOSDAQ"
        """
        data = pykrx_source.get_market_index(index_name)
        if not data:
            return f"No data available for index '{index_name}'"

        lines = [
            f"**{data['name']}** Index",
            f"Value: {data['close']:,.2f}",
            f"Date: {data['date']}",
        ]
        if "change" in data:
            lines.append(f"Change: {data['change']:+,.2f} ({format_pct(data['change_pct'])})")
        if data.get("volume"):
            lines.append(f"Volume: {format_volume(data['volume'])}")
        return "\n".join(lines)

    @mcp.tool()
    def market_cap(ticker: str) -> str:
        """Get market capitalization data for a stock.

        Args:
            ticker: 6-digit stock ticker (e.g., "005930")
        """
        data = pykrx_source.get_market_cap(ticker)
        if not data:
            return f"No market cap data for {ticker}"

        # Try to get stock name
        matches = pykrx_source.search_ticker(ticker)
        name = matches[0]["name"] if matches else ticker

        return "\n".join([
            f"**{name}** ({ticker})",
            f"Market Cap: {format_krw(data['market_cap'])}",
            f"Shares Outstanding: {data['shares_outstanding']:,}",
            f"Volume: {format_volume(data['volume'])}",
            f"Date: {data['date']}",
        ])
