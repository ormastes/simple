# MCP debug adapter layer expert

Owner: release100_memory_mcp_lsp / debug_truth.

Read `doc/07_guide/tooling/mcp_debug_operation_truthfulness.md` before changing
`src/app/mcp/main_lazy_debug_tools.spl`. Preserve the shared authority boundary:
authorize through DebugServiceV1, record actual outcome, and return explicit
unsupported/denied tool errors when no target transport exists. Never turn
backend catalog capabilities, bootstrap plans or process spawn into observation
or execution success. A real future backend must replace refusal with a
source/build/epoch-bound target response and executable end-to-end evidence.

The focused spec is `test/01_unit/app/mcp_unit/mcp_debug_truth_spec.spl`.
Runtime verification is pending; no source-only PASS claim is permitted.
