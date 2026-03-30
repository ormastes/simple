# obsidian-search Claude Plugin

Claude Code plugin bundle for the Obsidian vault MCP and bridge servers.

## Install

This plugin is intended for use from a Simple repository checkout. It needs a
valid `OBSIDIAN_VAULT_PATH` and launches the checked-in example servers:

```bash
bin/simple run examples/obsidian-search/src/main.spl
bin/simple run examples/obsidian-search/src/main_bridge.spl
bin/simple run examples/obsidian-search/src/main_lsp.spl
```

## Included Servers

- `obsidian-search`: vault search and note tooling
- `obsidian-lsp-mcp`: LSP-oriented MCP bridge for diagnostics and completions
