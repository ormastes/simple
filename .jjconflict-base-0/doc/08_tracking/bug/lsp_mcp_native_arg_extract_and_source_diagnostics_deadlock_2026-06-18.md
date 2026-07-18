# Bug: simple-lsp-mcp native tools/call broken + source-mode diagnostics deadlock

- **Filed:** 2026-06-18
- **Severity:** P1 (LSP MCP tools unusable on native; diagnostics unusable in source mode)
- **Components:** `src/app/simple_lsp_mcp/`, native AOT codegen, interpreter `process_run`

## Symptom

Two distinct, independent defects in `simple-lsp-mcp`:

### 1. Native binary fails every tools/call ("Missing tool name")

`bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server` answers `initialize`
and `tools/list` (11 tools), but **every `tools/call` returns
`{"content":[{"type":"text","text":"Missing tool name"}],"isError":true}`**.
Verified three ways: live MCP tool call, direct binary pipe, and via
`bin/mcp_stdio_bridge.js`. Same AOT arg-extraction codegen bug family as the
native `simple_mcp_server` ("Missing tool name" / `app_extract_str` returns "" /
`text.index_of` folds in the full-program native build).

A green `claude mcp list` / `tools/list` count is NOT proof tools work — the
prior "lsp_tools_count=11, verified" was a false-green (the smoke check
(`scripts/check/check-mcp-native-smoke.shs`) only counts `tools/list` + framing,
never runs a real `tools/call`).

### 2. Source mode: lsp_diagnostics deadlocks the server

Running from source (`bin/simple run src/app/simple_lsp_mcp/main.spl`) fixes
10/11 tools (symbols, hover, definition, references, completions, type-at,
signature-help, document-highlight, type-definition, implementation,
folding-range — all run a plain `simple <script.spl> ...` via `process_run` and
work). But **`lsp_diagnostics` hangs the whole server**: it shells out to
`simple check <file>` (`run_lsp_diagnostics`, tools.spl), and the interpreter's
`process_run` never completes — the spawned child becomes a **zombie**
(`[simple-main] <defunct>`) while the parent stays in **`futex_wait`** forever.

Reproduces regardless of: the spawned binary (`SIMPLE_BINARY=…/simple_seed`
still hangs), and an `sh -c '<bin> check <file> >tmp 2>&1 </dev/null'`
output-to-file redirect (still hangs — so it is not a stdout/stderr pipe-EOF
issue). `simple check <file>` standalone is ~0.13s, so it is not slowness.

The split — `simple <script.spl>` spawns return fine, `simple check`
(a CLI subcommand that itself spawns a delegate via `_cli_driver_binary()`)
deadlocks — points at the interaction between the no-GC interpreter's
`process_run` wait and a subcommand that double-spawns / hits the stage4
self-exec guard (cf. `stage4-self-exec-fork-bomb`,
`stage4-test-needs-seed-driver`). Root fix lives in the Rust runtime
`process_run`/subprocess-wait path, not in `.spl`.

## Current mitigation (shipped 2026-06-18)

- All launch paths (`config/mcp/install.shs` `.mcp.json` + Codex; `scripts/setup/setup.shs`
  generated `bin/simple_lsp_mcp_server`; `bin/simple_lsp_mcp_server.cmd`; templates) wire
  `simple-lsp-mcp` to **source mode** (`bin/simple run src/app/simple_lsp_mcp/main.spl`).
  Native is opt-in via `SIMPLE_LSP_MCP_PREFER_NATIVE=1`.
- `run_lsp_diagnostics` is **gated off** unless `SIMPLE_LSP_ENABLE_DIAGNOSTICS=1`: it returns
  a clear "diagnostics unavailable in source mode … run `simple check <file>` directly"
  message instead of spawning `simple check` and hanging the server.
- 2026-06-22 hardening: the opt-in diagnostics path now uses
  `process_run_timeout(..., 10000)` instead of the unbounded `process_run`, so
  an accidental enable cannot wedge the LSP MCP server indefinitely. Guarded by
  `test/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.spl`.

So 10/11 LSP tools work today; `lsp_diagnostics` is degraded to a message (no hang).

## Real fixes (pending)

1. Fix the native AOT arg-extraction codegen so `tools/call` extracts the tool
   name (shared with `mcp_full_program_native_codegen_and_arg_extract_2026-06-16`;
   real path is the Rust LLVM backend per that doc). Then re-enable native via
   `SIMPLE_LSP_MCP_PREFER_NATIVE=1`.
2. Fix the interpreter `process_run` deadlock when the spawned process itself
   spawns a delegate (zombie child + parent `futex_wait`). Then re-enable
   diagnostics via `SIMPLE_LSP_ENABLE_DIAGNOSTICS=1`.

## Repro

```sh
# native: Missing tool name
printf '%s\n' \
 '{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2024-11-05","capabilities":{},"clientInfo":{"name":"p","version":"0"}}}' \
 '{"jsonrpc":"2.0","method":"notifications/initialized"}' \
 '{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"lsp_symbols","arguments":{"file":"src/app/mcp/main.spl"}}}' \
 | bin/release/x86_64-unknown-linux-gnu/simple_lsp_mcp_server

# source diagnostics: hang (zombie child + parent futex_wait) — only with the gate disabled
SIMPLE_LSP_ENABLE_DIAGNOSTICS=1 SIMPLE_LIB=$PWD/src bin/simple run src/app/simple_lsp_mcp/main.spl  # then send lsp_diagnostics
```

## 2026-07-16 hardening evidence

- The arm64 Darwin native artifact still lists all 11 tools but returns
  `Missing tool name` for an exact `lsp_symbols` call. This confirms the
  advertised-tool false green on the current macOS artifact.
- `json_helpers.spl` now uses direct text slices for field extraction. The
  previous character-by-character concatenation is the AOT-sensitive path;
  focused source checking passes and a regression spec covers a standard
  `tools/call` plus numeric and string request IDs. A fresh native artifact is
  still required before this source correction can close the bug.
- The generated wrapper probe cache version is bumped and a native candidate
  must now pass initialize, tools/list, and a correlated real `lsp_symbols`
  call. Both existing Darwin candidates were rejected by that probe, so
  `SIMPLE_LSP_MCP_PREFER_NATIVE=1` fails closed instead of caching a broken
  binary. Standard Darwin release candidates are checked before the legacy
  Mach-O platform directory.

## Runtime verification (2026-07-17)

Native `simple_lsp_mcp_server` (x86_64-unknown-linux-gnu): `initialize` answers correctly; real `tools/call` (`lsp_symbols`) returns `{"content":[{"type":"text","text":"Missing tool name"}],"isError":true}` (defect 1 STILL-REPRODUCES, exact match). Source-level: `SIMPLE_LSP_ENABLE_DIAGNOSTICS` gate and "diagnostics unavailable in source mode" message confirmed present at `src/app/simple_lsp_mcp/tools.spl:41-43` (mitigation in place); underlying deadlock (defect 2) not independently triggered (risk of unbounded hang exceeded budget).

### macOS wrapper smoke follow-up

The production MCP wrapper passes startup, request-ID correlation, schema,
functional-call, and 153-tool checks. Its framing validator was separately
fixed to inspect `file_read_bytes` because `file_read` normalizes CRLF and the
deployed interpreter's `text_to_bytes` exposes internal four-byte text units.
The LSP wrapper still exits 1: both existing Darwin native candidates fail the
real-call probe, then source fallback reaches the stale deployed compiler and
reports `unknown extern function: rt_cli_arg_count`. A fresh Stage 4 deploy is
therefore still required before the current LSP source can be verified.
