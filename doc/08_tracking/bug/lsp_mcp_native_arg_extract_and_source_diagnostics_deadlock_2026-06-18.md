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

So 10/11 LSP tools work today; `lsp_diagnostics` is degraded to a message (no hang).

## Real fixes (pending)

1. Fix the native AOT arg-extraction codegen so `tools/call` extracts the tool
   name (shared with `mcp_full_program_native_codegen_and_arg_extract_2026-06-16`;
   real path is the Rust LLVM backend per that doc). Then re-enable native via
   `SIMPLE_LSP_MCP_PREFER_NATIVE=1`.
2. Fix the interpreter `process_run` deadlock when the spawned process itself
   spawns a delegate (zombie child + parent `futex_wait`). Then re-enable
   diagnostics via `SIMPLE_LSP_ENABLE_DIAGNOSTICS=1`.

## Runtime fix landed 2026-06-18 (pending rebuild+deploy)

Root cause confirmed in the C runtime: `rt_process_run` (`src/runtime/runtime_native.c`)
used `popen()` + `fgets()`-until-EOF. `pclose()` reaps the shell fine, but `fgets`
blocks forever when a reparented descendant (e.g. `simple check`'s delegate driver)
keeps the stdout pipe write-end open, so EOF never arrives.

Fix: read the pipe via `poll()` with a 3s idle timeout instead of `fgets`-to-EOF.
Real EOF (all write-ends closed) still breaks immediately — no added latency for the
common case — but a descendant-held pipe now returns after the stream goes idle
(capturing the command's output) instead of hanging. Validated in a standalone C
harness: a normal command returns instantly with full output; a command that
backgrounds a 30s descendant returns in ~3s with its output intact (no hang).

NOT yet live: `rt_process_run` is the C runtime baked into the self-hosted `bin/simple`,
so the fix requires rebuilding `libsimple_runtime.a` and relinking `bin/simple`
(full bootstrap). Until then `lsp_diagnostics` stays gated off. After deploy, flip the
gate (remove the `SIMPLE_LSP_ENABLE_DIAGNOSTICS` guard in `run_lsp_diagnostics`).
Parity TODO: the Rust interpreter `rt_process_run` (`interpreter_extern/system.rs`,
`Command::output()`) has the same EOF-wait issue on the cargo-seed path.

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
