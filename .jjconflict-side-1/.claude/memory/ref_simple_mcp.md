---
name: Simple MCP Server Reference
description: MCP server architecture, 99 tools list, tool-to-CLI mapping, configuration
type: reference
---

## MCP Server
- Location: `src/app/mcp/main.spl` (273 lines, optimized)
- Binary: `bin/simple_mcp_server_optimized`
- Startup: <800ms, tool list <10ms, first call <200ms

## MCP is a thin wrapper
Most tools delegate to `bin/simple` CLI or shell commands:

| MCP Tool | Backed By |
|----------|-----------|
| `simple_check`, `simple_diagnostics` | `bin/simple query check` |
| `simple_ast_query` | `bin/simple query ast-query` |
| `simple_sem_query` | `bin/simple query sem-query` |
| `simple_search` | `grep -rn` (NOT query engine) |
| `simple_api` | `find + grep` (NOT query engine) |
| `simple_symbols` | In-process line scan |
| `simple_dependencies` | In-process imports + grep |
| `simple_test/build/fmt/lint/fix/doc_coverage` | `bin/simple` CLI |
| VCS tools (diff/log/commit/push/etc.) | `jj` commands |
| Debug tools (19) | DAP protocol / in-process state |
| Task tools (3) | In-process background manager (MCP-only) |
| Test daemon tools (4) | `bin/simple test-daemon` |

## Configuration (`.mcp.json`)
```json
{"mcpServers": {"simple-mcp": {"command": "bin/simple", "args": ["src/app/mcp/main.spl", "server"]}}}
```

## CLI Mode
```bash
bin/simple src/app/mcp/main.spl search "pattern"
bin/simple src/app/mcp/main.spl read file.spl
bin/simple src/app/mcp/main.spl file_info file.spl
```

## Files
`src/app/mcp/main.spl` + `main_lazy_*.spl` (10 files: json, protocol, diag_tools, query_tools, vcs_tools, cli_tools, debug_tools, debug_log_tools, tasks, test_daemon_tools)
