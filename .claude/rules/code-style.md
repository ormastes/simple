---
alwaysApply: true
---
# Code Style

- **NEVER over-engineer** - only make requested changes
- **NEVER add unused code** - delete completely
- **Logs are NOT unused code** — never delete debug/probe/perf log inserts during cleanup; convert them to level-gated logs (default off). Delete only one-off non-reusable dumps. See doc/07_guide/infra/logging/log_retention_policy.md
- **DO NOT ADD REPORT TO GIT** unless requested
- **NEVER convert TODO/FIXME to NOTE** - implement or delete entirely
- **Never mutate a collection through a temporary alias.** Simple's value semantics are copy-on-write, so `val t = self.table; t.push(x); self.table = t`, `self.xs = f(self.xs, v)`, and `.keys()`/`.values()` inside a loop body each deep-copy the WHOLE collection per write — O(n) per operation, invisible on small fixtures, catastrophic at real scale. Mutate through the single owner (`self.table.push(x)`, `self.a[i].b[k] = v`) and hoist `.keys()` above the loop. Ratcheted by `sh scripts/check/check-cow-alias-hotpath.shs`; analysis in `doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`.
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

## Native-Codegen Dict Pitfalls (2026-07-27, RESOLVED 2026-08-09)

Under **native** codegen (not the interpreter, not the seed), `Dict.len()`
used to always return `-1`, and `.get(k)` on a hit used to be corrupt
(undecoded `i64`, or a segfaulting struct/class/enum payload). **Both are
fixed** (`.len()` routing fix 2026-08-01; `.get()` hit-decode fix
`7e83e92ce31`) and re-verified via real JIT execution on 2026-08-09 — see the
RESOLVED note at the top of `doc/07_guide/language/dict_native_pitfalls.md`
for evidence and commit references. `Dict.len()` and `.get()` on
struct/class/enum-valued dicts are now safe to call directly. Other
native-only Dict gaps (`f64`-value `.get()` miss, class-field `d[k]`
bracket-read on array values) remain open — see that doc's truth table
before relying on those specific operations.
