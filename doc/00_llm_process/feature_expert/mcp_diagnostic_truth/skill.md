# MCP diagnostic compatibility owner

Owner: src/app/mcp/main_lazy_diag_tools.spl. Use file_read_result for empty/read-error distinction. Both text/JSON legacy diagnostic paths use _diag_location_colons; preserve warnings regardless of exit zero. diagnostic_check_status separates failure/timeout/missing evidence from parsed findings. Never infer canonical clean status from an empty or arbitrary text payload.

Focused specs: test/01_unit/app/mcp_unit/mcp_diagnostic_truth_spec.spl. Runtime verification and public MCP admission pending; see doc/08_tracking/bug/mcp_reader_diagnostic_truth_2026-11-06.md. Source-view session/projection work is a separate shared owner.
