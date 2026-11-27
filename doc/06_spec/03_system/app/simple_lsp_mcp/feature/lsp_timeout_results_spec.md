# LSP timeout response protocol boundary

Manual companion for
`test/03_system/app/simple_lsp_mcp/feature/lsp_timeout_results_spec.spl`.
Requirement: REQ-LSP-TIMEOUT-RESULT-001.
Status: authored, UNRUN; this manual is not generated execution evidence.

| Scenario | Setup and assertion |
| --- | --- |
| Incomplete diagnostics | Feed the production diagnostics normalizer partial warning stdout, the bounded owner timeout marker, and exit -1. Build the production response and parse it: id 42, code -32001, exact 10000 ms message, no result, partial warning, or diagnostic block. |
| Independent response construction | Build a timed-out query response, then successful symbol content with id 51. The second response has no error and retains the new content. This checks stateless helper composition, not the stdio loop. |

Live child deadline, later ping, and descendant cleanup evidence belongs to
`test/02_integration/app/simple_lsp_mcp/lsp_process_lifecycle_test.cjs` with an
explicit qualified native server. It remains TEST_BLOCKED until that producer
is available. See the [bug record](../../../../../08_tracking/bug/lsp_mcp_nonposition_timeout_success_2026_11_03.md).
