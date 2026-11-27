# Caret essential-app gate specs contradicted the landed launch guard (2026-11-22)

Status: FIXED in specs (this change). Gemini/Kimi launch coverage stays absent until
provider adapters land.

## Symptom

Phase 1 seed, `check-caret-suite-bootstrap.shs` lanes replicated by hand:

- `test/03_system/llm_caret_agent_backends_spec.spl` (provider-wrappers lane): 4/6, gemini and
  kimi scenarios `expected not_started to equal started`.
- `test/03_system/llm_caret_multi_manager_spec.spl` (multi-manager lane): 2/3,
  `expected not_started to equal running`, `expected stop_failed to equal stopped`.

## Root cause

`346107f1c53` ("refuse unsupported legacy provider launches before effects") added
`agent_plan_launch_error_v1` (`src/app/llm_caret/agent_plan.spl:76`). Per
REQ-CARET-LAUNCH-002 (`doc/05_design/caret_provider_launch_guard.md`), any provider other
than claude/claude_cli/codex returns `provider_adapter_required:<provider>` before spawn,
and a batch containing one is rolled back (REQ-CARET-LAUNCH-003). The two gate specs predate
the guard and still asserted that Claude-style argv is spawned for Gemini and Kimi. The design
doc records its own scenarios as UNRUN, which is how the gate drift went unnoticed.

## Fix

- agent backends: gemini/kimi scenarios now assert the refusal (`not_started`,
  `provider_adapter_required:<provider>`, `pid == -1`).
- multi manager: the first scenario launches the supported claude+codex pair (running, 2 panes,
  stop -> stopped) and asserts a batch that adds gemini/kimi is `not_started` /
  `launch_rolled_back`.
- Scenario counts stay 6 and 3, so `check-caret-suite-bootstrap.shs --self-test` still passes.

Canonical regression for the guard: `test/03_system/app/llm_caret/feature/provider_launch_authority_spec.spl`
(6/6 on Phase 1). After the change: agent backends 6/6, multi manager 3/3.

Open follow-up: restore real Gemini/Kimi spawn coverage when provider adapters exist.
