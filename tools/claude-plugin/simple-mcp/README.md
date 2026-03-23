# simple-mcp Claude Plugin

Claude Code MCP plugin bundle for the Simple project server.

## Install

Use the checked-in local marketplace from a Simple repo checkout:

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-mcp@simple-local
```

This plugin launches:

```bash
bin/simple_mcp_server
```

from the workspace root.

## Included Server

- `simple-mcp`: main Simple MCP server for code query, build, test, diagnostics, and project tooling
