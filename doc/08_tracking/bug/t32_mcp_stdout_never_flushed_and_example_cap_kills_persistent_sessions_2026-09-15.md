# t32 MCP servers: stdout never flushed, and the examples/ 10s run cap kills persistent stdio sessions

- **Filed:** 2026-09-15
- **Status:** FIXED 2026-09-15 (stdout flush in both protocol writers;
  `SIMPLE_TIMEOUT_SECONDS=0` default in both Windows t32 wrappers and in
  `.kimi-code/mcp.json`). The deeper "example timeout applies to long-running
  servers" design defect is worked around, not redesigned.
- **Severity:** high — t32 MCP was unusable under EVERY persistent-stdio MCP
  client (Kimi Code, Claude Code). It answered only to pipe-and-close-stdin
  probes, which is how the 2026-09-13 "verified 35 tools" measurement passed
  while real clients hung or lost the server at 10s.
- **Host:** Windows 11, `bin/release/x86_64-pc-windows-msvc/simple.exe`
  (Rust-built bootstrap seed warning is expected noise on this binary)

## Symptom

Under a real MCP client (stdin held open for the session lifetime):

1. `t32_write_stdout_message` / `lsp_write_stdout_message`
   (`examples/10_tooling/trace32_tools/t32_mcp/protocol.spl:95`,
   `t32_lsp_mcp/protocol.spl:68`) used `print_raw(...)` and never
   `rt_stdout_flush()`. Responses sat in the block-buffered stdout buffer
   until process exit, so `initialize` never got an answer: clients saw a
   hang. The servers flushed *stderr* explicitly (`rt_stderr_flush()`), which
   made the startup log look alive while stdout was silent — the debugging
   trap that cost this diagnosis most of a day.
2. Once the flush was fixed, the servers answered `initialize` (~2s) and then
   died at exactly 10s with
   `debug: writing response error: example timed out after 10s: examples/10_tooling/trace32_tools/t32_mcp/main.spl`.
   Any entry point under `examples/` runs under the example-mode budget
   (`SIMPLE_TIMEOUT_SECONDS`, default 10s) — a total run cap, not an idle
   timeout. A stdio MCP session always outlives 10s.

## Measured (2026-09-15, node spawn shell:false, cwd = repo root)

| configuration | initialize | tools/list | fate |
|---|---|---|---|
| before fix, stdin open | none in 420s | — | hang (buffered) |
| after flush fix only, stdin open | ~10s | — | killed by 10s example cap |
| flush fix + `SIMPLE_TIMEOUT_SECONDS=0`, stdin open | t32-mcp 2.2s / t32-lsp 1.8s | 36 / 6 tools | healthy |
| any fix, stdin closed (pipe) | ~3–10s | 36 / 6 tools | clean EOF exit (this is why 2026-09-13 "passed") |

## Fixes applied

- `examples/10_tooling/trace32_tools/t32_mcp/protocol.spl` — `rt_stdout_flush()`
  at the end of `t32_write_stdout_message`.
- `examples/10_tooling/trace32_tools/t32_lsp_mcp/protocol.spl` — added the
  `extern fn rt_stdout_flush()` declaration and the same call in
  `lsp_write_stdout_message`.
- `bin/release/x86_64-pc-windows-msvc/t32_mcp_server.cmd` and
  `t32_lsp_mcp_server.cmd` — default `SIMPLE_TIMEOUT_SECONDS` to `0`
  (disable) when unset, with a comment pointing here. Same env is set
  explicitly on the t32 entries in `.kimi-code/mcp.json` (the Kimi Code
  project layer), which bypasses wrappers.
- POSIX sh wrappers for t32 were NOT touched: per the root `.mcp.json` `_info`,
  the POSIX t32 path already exits 127 there unless a hash-admitted native is
  built, so the env default has nothing to protect yet.

## Follow-ups (not done here)

- The example-run cap applying to long-lived servers is a design smell:
  either the cap should be idle-based, or server entry points under
  `examples/` should opt out. The `SIMPLE_TIMEOUT_SECONDS=0` default is the
  documented escape hatch used by multi-hour bootstrap runs.
- Other example-tree MCP-ish servers (if any are added) need the same two
  treatments: flush after every protocol write, and no example cap.
