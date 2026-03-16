"""Korean Stock Market MCP Server — FastMCP entry point."""

from __future__ import annotations

from mcp.server.fastmcp import FastMCP

from korean_stock_mcp.tools import price, search, market, financials, news, analysis

mcp = FastMCP(
    "Korean Stock Market",
    instructions="Korean stock market data — prices, financials, news for KOSPI/KOSDAQ",
)

# Register all tool modules
price.register(mcp)
search.register(mcp)
market.register(mcp)
financials.register(mcp)
news.register(mcp)
analysis.register(mcp)


def main() -> None:
    """Run the MCP server on stdio transport."""
    mcp.run(transport="stdio")


if __name__ == "__main__":
    main()
