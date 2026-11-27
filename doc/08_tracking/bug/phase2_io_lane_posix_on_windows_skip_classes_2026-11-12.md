# Phase-2 io lane: POSIX-on-Windows skip classes (2026-11-12)

- **Status:** OPEN — host-capability gaps, tracked for the POSIX qualification lane
- **Found:** 2026-11-12, release/1.0.0 Windows seed sweep (integration lane 1b)

The `test/02_integration/io/` lane runs POSIX file/text semantics that the
Windows host honestly does not provide. Two classes:

1. **SOSIX host text provider unavailable on Windows** (product reports
   `TextIoError::Unsupported(SOSIX ordinary UTF-8 host text provider
   unavailable: windows)`), plus a seed runtime error
   `rt_env_set: value must be a string` in the env-distinction example:
   - `io/sosix_stdin_session_spec.spl` (0/17)
   - `io/sosix_tool_text_spec.spl` (0/11)
2. **POSIX mode/append semantics on Windows** (`expected 420 to equal 128` —
   0644-vs-0200 creation modes; empty-append file creation):
   - `io/external_file_io_spec.spl` (9/11)
   - `io/external_text_io_spec.spl` (3/4 — also covers the malformed-text
     oracle)
   - `io/file_handle_nullable_read_spec.spl` (3/4)
   - `io/file_text_session_spec.spl` (19/21)

These specs presumably qualify the POSIX/SOSIX lanes and are expected to pass
on unix hosts. They are recorded here so the Windows phase accounting counts
them as host-blocked, not regressions. A future lane may either host-gate the
examples (skip on non-POSIX, like worker_timeout_cleanup_spec) or extend the
Windows providers.

## Addendum: simple_lsp_mcp_log_modes_spec (qualification-env)

`test/02_integration/app/simple_lsp_mcp_log_modes_spec.spl` requires the
compiled native server via `SIMPLE_LSP_MCP_TEST_BINARY` (its header: "raw
-source execution is not evidence"). No `simple_lsp_mcp_server.exe` is built
on this host, so all 5 examples time out (-1) here. Expected-red without
qualification; not a product bug.
