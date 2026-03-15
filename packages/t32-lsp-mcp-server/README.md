# @simple-lang/t32-lsp-mcp-server

CMM/PRACTICE language intelligence via [Model Context Protocol](https://modelcontextprotocol.io).

Provides 6 tools for parsing, diagnostics, completions, hover, symbols, and CLI validation for TRACE32 PRACTICE scripts.

## Installation

```bash
npm install -g @simple-lang/t32-lsp-mcp-server
```

## Usage with Claude Desktop

```json
{
  "mcpServers": {
    "cmm-lsp": {
      "command": "t32-lsp-mcp-server"
    }
  }
}
```

## License

MIT
