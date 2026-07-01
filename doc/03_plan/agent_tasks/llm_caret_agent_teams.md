# LLM Caret Agent Teams - Agent Tasks

Date: 2026-07-01

## Tasks

- Implement `src/app/llm_caret/agent_plan.spl`.
- Implement `src/app/llm_caret/agent_files.spl`.
- Implement `src/app/llm_caret/agent_vcs.spl`.
- Implement `src/app/llm_caret/agent_discovery.spl`.
- Implement `src/app/llm_caret/agent_mailbox.spl`.
- Implement `src/app/llm_caret/agent_runtime.spl`.
- Add `test/01_unit/app/llm_caret/agent_plan_spec.spl`.
- Update LLM Caret guide and skills with the static-planning contract.

## Sidecars

N/A for this slice: one pure module plus one unit spec. Merge owner: Codex.
Final reviewer: normal/highest-capability Codex review.

## Deferred

Persistent process teams, background VCS watching, plugin install execution,
live MCP registry discovery, and team message transport need separate
implementation tasks.
