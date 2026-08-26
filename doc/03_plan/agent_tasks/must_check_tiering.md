# Must-Check Tiering Agent Tasks

- `bootstrap_phase_audit`: read-only Stage 1-4 receipt mapping — complete.
- `push_budget_audit`: read-only fail-closed and timing audit — complete.
- `must_check_tests_docs`: read-only test/manual/wiki routing — complete.
- Merge owner and final reviewer: primary Codex agent.
- Generated-manual reviewer: primary Codex agent.
- `.agents/skills/`: N/A — no agent-side `sp_dev` skill exists; the shared
  implementation and verification skills do not define the must-check ledger.
- `.claude/commands/`: N/A — SPipe development routing is agent/skill owned in
  this repository; the Gemini command and Codex/Claude SPipe instructions are
  the applicable command surfaces.

Shared interfaces: `push_must_check`, `bootstrap_must_check`, and
`must_check_ledger`. Manual helpers: `step("Run the lightweight push
must-check")`, `step("Run the bootstrap must-check")`, and `step("Validate the
must-check ledger")`. No implementation placeholder may pass; use `fail(...)`.
