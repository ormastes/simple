---
alwaysApply: true
---
# Code Style

- **NEVER over-engineer** - only make requested changes
- **NEVER add unused code** - delete completely
- **Logs are NOT unused code** — never delete debug/probe/perf log inserts during cleanup; convert them to level-gated logs (default off). Delete only one-off non-reusable dumps. See doc/07_guide/infra/logging/log_retention_policy.md
- **DO NOT ADD REPORT TO GIT** unless requested
- **NEVER convert TODO/FIXME to NOTE** - implement or delete entirely
- For MCP/LSP/tool-server work: review startup path, hot request paths, cache strategy, startup/latency/RSS targets
- Production wrappers should execute cached compiled artifacts, not raw source
- Verify perf-sensitive tooling with warm startup time, request latency, and max RSS

## MCP Servers (`.mcp.json`)
| Server | Binary | Purpose | npm Package |
|--------|--------|---------|-------------|
| `simple-mcp` | `bin/simple_mcp_server` | Compiler MCP | `@simple-lang/mcp-server` |
| `simple-lsp-mcp` | `bin/simple_lsp_mcp_server` | LSP via MCP bridge | `@simple-lang/lsp-mcp-server` |
| `t32-mcp` | `bin/t32_mcp_server` | TRACE32 CMM/PRACTICE MCP | `@simple-lang/t32-mcp-server` |
| `t32-lsp-mcp` | `bin/t32_lsp_mcp_server` | TRACE32 LSP via MCP | `@simple-lang/t32-lsp-mcp-server` |
| `obsidian-lsp-mcp` | (separate package, on its own version track) | Obsidian LSP via MCP | `@simple-lang/obsidian-lsp-mcp-server` |

- `.mcp.json` launches `simple-lsp-mcp` from `bin/release/linux-x86_64/` (gitignored), but builds deploy to `bin/release/x86_64-unknown-linux-gnu/` — after rebuilding an MCP server, re-copy it to the launch path (`cp` to `.new` + `mv`; direct `cp` hits "Text file busy"). See `doc/07_guide/app/mcp/mcp.md` § Troubleshooting.

## AI CLI Plugins
- Claude plugins: `tools/claude-plugin/`
- Gemini extension: `gemini-extension.json`
- MCP registry: `tools/mcp-registry/`
