"""News MCP tools — Tier 3 (no API key required)."""

from __future__ import annotations

from mcp.server.fastmcp import FastMCP

from korean_stock_mcp.sources import news_source, pykrx_source


def register(mcp: FastMCP) -> None:
    """Register news tools with the MCP server."""

    @mcp.tool()
    def market_news(limit: int = 10) -> str:
        """Get latest Korean stock market news headlines.

        Args:
            limit: Number of articles (max 20, default 10)
        """
        limit = min(limit, 20)
        articles = news_source.get_market_news(limit)
        if not articles:
            return "No market news available"

        lines = [f"Korean Stock Market News ({len(articles)} articles)", ""]
        for i, article in enumerate(articles, 1):
            lines.append(f"{i}. **{article['title']}**")
            if article.get("source"):
                lines.append(f"   Source: {article['source']}")
            if article.get("published"):
                lines.append(f"   Published: {article['published']}")
            if article.get("link"):
                lines.append(f"   Link: {article['link']}")
            lines.append("")
        return "\n".join(lines)

    @mcp.tool()
    def stock_news(ticker: str, limit: int = 10) -> str:
        """Get news for a specific stock from Naver Finance.

        Args:
            ticker: 6-digit stock ticker (e.g., "005930")
            limit: Number of articles (max 20, default 10)
        """
        limit = min(limit, 20)

        # Get stock name for display
        matches = pykrx_source.search_ticker(ticker)
        name = matches[0]["name"] if matches else ticker

        articles = news_source.get_stock_news(ticker, limit)
        if not articles:
            return f"No news found for {name} ({ticker})"

        lines = [f"News for **{name}** ({ticker}) — {len(articles)} articles", ""]
        for i, article in enumerate(articles, 1):
            lines.append(f"{i}. **{article['title']}**")
            if article.get("source"):
                lines.append(f"   Source: {article['source']}")
            if article.get("date"):
                lines.append(f"   Date: {article['date']}")
            if article.get("link"):
                lines.append(f"   Link: {article['link']}")
            lines.append("")
        return "\n".join(lines)
