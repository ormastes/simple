# LSP nonposition child timeouts returned as success

- Bug: `lsp_mcp_nonposition_timeout_success_2026_11_03` (P2).
- Owner: `src/app/simple_lsp_mcp/tools.spl`.
- Status: source repair candidate; behavioral verification pending.
- Claim: `codex-lsp-timeout-results-20261103`.
- Base: `ef01ba93172`; found by Windows source review on 2026-11-03.
- Requirement: REQ-LSP-TIMEOUT-RESULT-001 ? every query tool returns JSON-RPC
  error -32001 when its bounded child times out, preserving request ids and
  successful output. An incomplete diagnostics check publishes no diagnostic block.

## Defect and repair

This is the narrow residual documented in the PR #4984 follow-ups in
[lsp_mcp_hover_definition_hang_windows_2026-10-27.md](lsp_mcp_hover_definition_hang_windows_2026-10-27.md).
`run_command_text` already produces a timeout sentinel, but visibility, symbols
and SAML wrapped it in a successful tool result. Diagnostics also discarded the
bounded process timeout classification and could expose partial output as success.

The shared `command_result` owner now handles both position and nonposition tools.
`lsp_diagnostics_output` recognizes the existing bounded-process timeout contract
before considering partial stdout or stderr. `diagnostics_result` classifies the
sentinel before appending diagnostic blocks. Completed commands retain existing
success, empty-output and nonzero diagnostic-output behavior. Timeout limits remain
30 seconds for queries and 10 seconds for diagnostics. No process/env owner changed.

## Evidence and limitations

- Authored unit regression: `test/01_unit/app/simple_lsp_mcp/lsp_timeout_result_spec.spl`
  (7 scenarios): numeric/string ids; success/empty/malformed text; all three runtime
  timeout marker forms; non-timeout negative controls; completed diagnostics;
  timeout precedence; diagnostic-block compatibility.
- Authored composed-boundary regression:
  `test/03_system/app/simple_lsp_mcp/feature/lsp_timeout_results_spec.spl`
  (2 scenarios). These call production helpers and parse protocol output; they do
  not launch a child or prove a live server keeps serving.
- Updated actual-process regression:
  `test/02_integration/app/simple_lsp_mcp/lsp_process_lifecycle_test.cjs`.
  Diagnostics must return error -32001 and omit partial warnings; the three other
  nonposition tools run real hanging child fixtures and must return the same error
  with their 30-second budget. A ping follows each timeout. Existing descendant
  cleanup checks remain. Expected timeout cost is about 100 seconds in this suite.
- Independent source/test review: no remaining actionable finding after adding
  tracked query PIDs to the live harness failure cleanup.
- `scripts/audit/direct-env-runtime-guard.shs --working` and `--staged`: PASS.
- Staged whitespace, bug DB CRC32/claim consistency, manual link and zero
  executable specs under `doc/06_spec`: PASS.
- The CJS harness without an explicit admitted server reports `TEST_BLOCKED`.
  This worktree has no admitted self-hosted compiler/native LSP server supplied for
  the changed source. The Simple specs, compiler/lib/MCP/LSP checks, MCP stdio
  integration and core/native smoke gates remain UNRUN. No Rust seed fallback,
  runtime PASS, startup/latency/RSS qualification, or bug closure is claimed.

Resume with an admitted self-hosted runtime built from this source. Execute both
new Simple specs, the required core/MCP checks and native smokes, then run the CJS
suite with `node test/02_integration/app/simple_lsp_mcp/lsp_process_lifecycle_test.cjs --server <absolute-qualified-server>`.
