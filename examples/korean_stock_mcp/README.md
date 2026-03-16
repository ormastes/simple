# Korean Stock Market MCP Server

MCP server providing Korean stock market data (KOSPI/KOSDAQ) via pykrx, FinanceDataReader, DART, and KRX APIs.

## Quick Start

```bash
# Run with uv (auto-installs dependencies)
uv run korean-stock-mcp

# Or install and run
uv pip install -e .
korean-stock-mcp
```

## Tools

### Tier 1 — No API Key Required
| Tool | Description |
|------|-------------|
| `stock_price` | Current/latest price for a ticker or name |
| `stock_ohlcv` | Historical OHLCV data |
| `stock_search` | Search stocks by Korean/English name |
| `stock_list` | List all tickers in KOSPI/KOSDAQ |
| `market_index` | KOSPI/KOSDAQ index value |
| `market_cap` | Market capitalization data |
| `sector_performance` | Sector-level performance analysis |
| `stock_compare` | Compare multiple stocks |

### Tier 2 — Optional Free API Keys
| Tool | Description | Key Source |
|------|-------------|-----------|
| `company_info` | Company disclosures | [DART](https://opendart.fss.or.kr) |
| `financial_statements` | Financial reports | [DART](https://opendart.fss.or.kr) |

### Tier 3 — News (No Key)
| Tool | Description |
|------|-------------|
| `market_news` | Korean market headlines via RSS |
| `stock_news` | Stock-specific news from Naver Finance |

## API Key Registration

| API | URL | Cost | Approval |
|-----|-----|------|----------|
| DART | https://opendart.fss.or.kr | Free | Instant |
| KRX | https://open.krx.co.kr | Free | ~1 day |

Copy `.env.example` to `.env` and add your keys:
```bash
cp .env.example .env
```

## Claude Code Integration

Add to your project's `.mcp.json`:
```json
{
  "mcpServers": {
    "korean-stock": {
      "command": "uv",
      "args": ["--directory", "examples/korean_stock_mcp", "run", "korean-stock-mcp"]
    }
  }
}
```

## Development

```bash
uv run pytest          # Run tests
uv run pytest -v       # Verbose
```
