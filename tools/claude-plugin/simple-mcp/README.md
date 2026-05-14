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

The plugin launches:

```bash
bin/simple_mcp_server
```

from the workspace root.

If you want a direct non-plugin install, register the wrapper from the
repository checkout:

```bash
claude mcp add simple-mcp -- /absolute/path/to/simple/bin/simple_mcp_server
```

Hosted `bin/simple ... src/app/mcp/main.spl` execution is a legacy/debug path,
not the default registration model.

## Included Server

- `simple-mcp`: main Simple MCP server for code query, build, test, diagnostics, and project tooling
