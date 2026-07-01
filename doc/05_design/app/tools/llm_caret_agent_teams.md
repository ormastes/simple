# LLM Caret Agent Teams - Detail Design

Date: 2026-07-01

## Data

`AgentLaunchRequest` stores provider, agent markdown path, skill path, task,
model, session id, and extra args. `AgentLaunchPlan` stores provider, mode,
prompt, argv, and summary. `AgentReviewRequest` stores reviewer, changed files,
and guidance.

## Builders

- Single-agent launch: builds one prompt with agent, skill, and task fields.
- Team launch: concatenates member launch prompts and records interaction mode.
- Low-agent review: lists changed files supplied by caller; no filesystem scan.
- Claude advisor: returns provider `claude_cli`, mode `advisor`.
- Codex goal: returns provider `codex`, mode `goal`.

## Errors

This slice does not return `Result`; empty fields stay visible in deterministic
prompt text so callers/tests can catch missing configuration.

## Verification

`test/01_unit/app/llm_caret/agent_plan_spec.spl` covers all builders with pure
assertions. Live launch, cancellation, and diff capture need later specs.
