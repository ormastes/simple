"""Financial data MCP tools (Tier 2 — requires DART API key)."""

from __future__ import annotations

from mcp.server.fastmcp import FastMCP

from korean_stock_mcp.sources import dart_source


def register(mcp: FastMCP) -> None:
    """Register financial tools with the MCP server."""

    @mcp.tool()
    def company_info(ticker: str) -> str:
        """Get company information from DART (requires DART_API_KEY).

        Args:
            ticker: 6-digit stock ticker or DART corp code
        """
        data = dart_source.get_company_info(ticker)
        if data is None:
            if not dart_source._is_available():
                return "DART API key not configured. Set DART_API_KEY environment variable.\nGet a free key at: https://opendart.fss.or.kr"
            return f"No company info found for {ticker}"

        lines = [f"**{data['corp_name']}** ({data.get('corp_name_eng', '')})", ""]
        fields = [
            ("Stock Code", data.get("stock_code")),
            ("CEO", data.get("ceo_name")),
            ("Industry", data.get("industry")),
            ("Established", data.get("establishment_date")),
            ("Homepage", data.get("homepage")),
            ("Address", data.get("address")),
        ]
        for label, val in fields:
            if val:
                lines.append(f"- **{label}:** {val}")
        return "\n".join(lines)

    @mcp.tool()
    def financial_statements(
        ticker: str,
        year: str = "2024",
        report_type: str = "annual",
    ) -> str:
        """Get financial statements from DART (requires DART_API_KEY).

        Args:
            ticker: 6-digit stock ticker or DART corp code
            year: Business year (e.g., "2024")
            report_type: "annual", "semi", "q1", or "q3"
        """
        report_map = {
            "annual": "11011",
            "semi": "11012",
            "q1": "11013",
            "q3": "11014",
        }
        report_code = report_map.get(report_type, "11011")

        data = dart_source.get_financial_statements(ticker, year, report_code)
        if data is None:
            if not dart_source._is_available():
                return "DART API key not configured. Set DART_API_KEY environment variable.\nGet a free key at: https://opendart.fss.or.kr"
            return f"No financial data found for {ticker} ({year})"

        lines = [
            f"Financial Statements — {ticker} ({year}, {report_type})",
            "",
            "| Account | Current | Previous | Before Previous |",
            "|---------|---------|----------|-----------------|",
        ]
        for item in data:
            lines.append(
                f"| {item['account_name']} | {item['current_amount']} | "
                f"{item['previous_amount']} | {item['before_previous']} |"
            )
        return "\n".join(lines)
