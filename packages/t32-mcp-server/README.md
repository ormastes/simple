# @simple-lang/t32-mcp-server

TRACE32 debug session control via [Model Context Protocol](https://modelcontextprotocol.io).

Provides 23 tools for session management, window capture, action invocation, field manipulation, headless setup, and command database.

**Note:** Requires a running TRACE32 instance with API access enabled.

## Installation

```bash
npm install -g @simple-lang/t32-mcp-server
```

## Usage with Claude Desktop

```json
{
  "mcpServers": {
    "trace32": {
      "command": "t32-mcp-server"
    }
  }
}
```

## License

MIT
