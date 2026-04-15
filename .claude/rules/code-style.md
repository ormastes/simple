---
alwaysApply: true
---
# Code Style

- **NEVER over-engineer** - only make requested changes
- **NEVER add unused code** - delete completely
- **DO NOT ADD REPORT TO GIT** unless requested
- **NEVER convert TODO/FIXME to NOTE** - implement or delete entirely
- For MCP/LSP/tool-server work: review startup path, hot request paths, cache strategy, startup/latency/RSS targets
- Production wrappers should execute cached compiled artifacts, not raw source
- Verify perf-sensitive tooling with warm startup time, request latency, and max RSS

## MCP Servers (`.mcp.json`)
| Server | Binary | Purpose |
|--------|--------|---------|
| `simple-mcp` | `bin/simple_mcp_server` | Compiler MCP |
| `simple-lsp-mcp` | `bin/simple_lsp_mcp_server` | LSP via MCP bridge |

## AI CLI Plugins
- Claude plugins: `tools/claude-plugin/`
- Gemini extension: `gemini-extension.json`
- MCP registry: `tools/mcp-registry/`
