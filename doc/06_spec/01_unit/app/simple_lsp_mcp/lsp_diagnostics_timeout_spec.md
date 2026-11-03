# LSP diagnostics process ownership

Status: AUTHORED_UNRUN. These scenarios require a qualified self-hosted runtime.
This manual was updated from source; it is not a generated execution receipt.

Source: `test/01_unit/app/simple_lsp_mcp/lsp_diagnostics_timeout_spec.spl`.

- Exact regression: opt-in diagnostics uses `process_run_bounded` with the
  original 10000 ms deadline and the existing 1 MiB capture bound; no
  `process_run_timeout` reference remains in the tools owner.
- Adjacent regression: `arg_int_field` returns 41 and 0 for valid positions and
  -1 for negative, nonnumeric, or missing positions.

Native behavioral gate:
`test/02_integration/app/simple_lsp_mcp/lsp_process_lifecycle_test.cjs`.
Supply an absolute qualified native server using `--server`. It checks six
cases: three initialized EOF exits, empty EOF, independent-client isolation,
and diagnostics timeout/descendant cleanup followed by ping and EOF exit.
The gate uses a real server and native subprocess owner with a Node delegate
fixture; it tracks only the PIDs it launched. Missing qualification exits 77
with TEST_BLOCKED, and is not a passing server check.

The original observed 48-process external spawner remains unidentified.
