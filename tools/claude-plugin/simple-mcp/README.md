# simple-mcp Claude Plugin

Claude Code MCP plugin bundle for the Simple project server.

## Install

Use the checked-in local marketplace from a Simple repo checkout:

```bash
claude plugin marketplace add tools/claude-plugin/marketplace
claude plugin install simple-mcp@simple-local
```

This plugin is not a standalone portable bundle. It expects to run from a
Simple repository root that contains:

- `bin/simple_mcp_server`
- `bin/release/simple` or `bin/release/linux-x86_64/simple`
- `src/app/mcp/main.spl`

The plugin launches:

```bash
bin/simple_mcp_server
```

from the workspace root.

If you want a direct non-plugin install, use the MCP registration flow from the
repository checkout instead:

```bash
claude mcp add simple-mcp -- \
  /absolute/path/to/simple/bin/release/simple \
  /absolute/path/to/simple/src/app/mcp/main.spl
```

## Included Server

- `simple-mcp`: main Simple MCP server for code query, build, test, diagnostics, and project tooling
