# Piped-process gaps blocking the stdin-held test-oracle ports (2026-11-27)

Status: open. Source: `python_phase_census_2026-11-27.md` rows classed BLOCKED.

The earlier "process_run cannot hold stdin open" note is stale. `std.nogc_sync_mut.io.process_ops`
already provides a long-lived piped child (`process_spawn_piped_result`,
`process_write_stdin_result`, `process_read_stdout_result`, `process_is_piped_alive_result`,
`process_piped_exit_status_v1`, `process_close_piped_result`), consumed by
`src/lib/editor/services/debug_session_dap.spl`. The remaining gaps for the blocked rows:

1. **Piped stderr read.** No `process_read_stderr*` on the piped path (stderr capture exists only on
   the owned-process v3 lease, which takes its input up front and cannot be written to later). The
   LSP/MCP gate requires `stderr == ""` and the term-byte `held` case asserts empty stderr.
2. **Byte-safe piped I/O.** Piped read/write take and return `text`; the term-byte fixtures use
   `00 c3 a9 0a 0d 0a ff`-class octets and the Content-Length framing needs exact byte counts. Needs
   `[u8]` variants.
3. **Environment on the piped path.** `process_spawn_environment_overlay_native_v1` is Windows-native
   only and returns -95 under the interpreter/JIT; `process_spawn_piped_result` takes no environment.
   The MCP wrapper sets `SIMPLE_MCP_TOOL_SET=all`.
4. **Bounded read with timeout** on the piped path (the Python gates wait `select`-style up to 5 s
   for a response while stdin stays open).

Blocked rows: `test/02_integration/app/{lsp,mcp}_native_stdio_protocol_test.py`,
`test/02_integration/app/fixtures/lsp_stdio_live_protocol_linux_evidence.py`,
`test/01_unit/runtime/windows_terminal_raw_bytes/{run-term-byte-fixtures,project-controlled-provider}.py`.

Not blocked by this, only by having a runnable binary: porting needs a built pure-Simple full CLI or
the target server binary on the host to prove parity; the seed cannot run them.
