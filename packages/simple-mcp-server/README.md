# @simple-lang/mcp-server

MCP server for the [Simple programming language](https://github.com/ormastes/simple).

Provides 75 tools for diagnostics, debugging, VCS, testing, analysis, agent loops, and team orchestration via the [Model Context Protocol](https://modelcontextprotocol.io).

## Installation

```bash
npm install -g @simple-lang/mcp-server
```

## Usage with Claude Desktop

Add to your Claude Desktop config (`claude_desktop_config.json`):

```json
{
  "mcpServers": {
    "simple": {
      "command": "simple-mcp-server"
    }
  }
}
```

## Requirements

- Simple compiler binary (auto-downloaded on install)
- Node.js >= 18

## License

MIT
