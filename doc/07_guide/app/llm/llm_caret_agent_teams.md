# LLM Caret Agent Teams

Date: 2026-07-01

Use `src/app/llm_caret/agent_plan.spl` for static agent/team request planning.

Supported builders:

- `build_agent_launch_plan` for one agent markdown path, skill path, task, provider, model, session, and extra args.
- `build_agent_team_plan` for a group of launch requests plus an interaction mode such as `btw-side`.
- `build_low_agent_review_plan` for reviewer guidance plus caller-supplied changed files or per-agent change sets.
- `build_claude_advisor_plan` for Claude advisor prompts.
- `build_codex_goal_plan` for Codex goal prompts.

This surface does not launch processes, scan diffs, persist teams, or provide a chat bus. Callers pass tracked files explicitly and hand the resulting prompt/argv to existing provider wrappers.

Default verification:

```bash
bin/release/simple test test/01_unit/app/llm_caret/agent_plan_spec.spl --mode=interpreter
bin/release/simple check src/app/llm_caret/agent_plan.spl
```
