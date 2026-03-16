"""Search and listing MCP tools."""

from __future__ import annotations

from mcp.server.fastmcp import FastMCP

from korean_stock_mcp.sources import pykrx_source


def register(mcp: FastMCP) -> None:
    """Register search tools with the MCP server."""

    @mcp.tool()
    def stock_search(query: str) -> str:
        """Search for Korean stocks by name or ticker.

        Args:
            query: Korean company name, English name, or partial ticker (e.g., "삼성", "samsung", "005930")
        """
        matches = pykrx_source.search_ticker(query)
        if not matches:
            return f"No stocks found matching '{query}'"

        lines = [f"Found {len(matches)} match(es) for '{query}':", ""]
        lines.append("| Ticker | Name | Market |")
        lines.append("|--------|------|--------|")
        for m in matches[:30]:
            lines.append(f"| {m['ticker']} | {m['name']} | {m['market']} |")
        if len(matches) > 30:
            lines.append(f"\n(Showing 30 of {len(matches)} results)")
        return "\n".join(lines)

    @mcp.tool()
    def stock_list(market: str = "ALL") -> str:
        """List all stocks in a Korean market.

        Args:
            market: "KOSPI", "KOSDAQ", or "ALL" (default)
        """
        tickers = pykrx_source.get_ticker_list(market.upper())
        if not tickers:
            return f"No tickers found for market '{market}'"

        lines = [f"Total: {len(tickers)} stocks in {market.upper()}", ""]

        # Group by market
        by_market: dict[str, list] = {}
        for t in tickers:
            by_market.setdefault(t["market"], []).append(t)

        for mkt, stocks in by_market.items():
            lines.append(f"\n### {mkt} ({len(stocks)} stocks)")
            lines.append("| Ticker | Name |")
            lines.append("|--------|------|")
            for s in stocks[:50]:
                lines.append(f"| {s['ticker']} | {s['name']} |")
            if len(stocks) > 50:
                lines.append(f"(... and {len(stocks) - 50} more)")

        return "\n".join(lines)
