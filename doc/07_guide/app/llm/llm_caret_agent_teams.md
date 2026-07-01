# LLM Caret Agent Teams

Date: 2026-07-01

Use `src/app/llm_caret/agent_plan.spl` for static agent/team request planning.

Supported builders:

- `build_agent_launch_plan` for one agent markdown path, skill path, task, provider, model, session, and extra args.
- `build_agent_capability_launch_plan` for explicit agent files, skill files, MCP servers, and plugins, mirroring SPipe handoffs.
- `build_agent_team_plan` for a group of launch requests plus an interaction mode such as `btw-side`.
- `build_btw_side_interaction_plan` for caller-supplied `btw` and `side` team transcript entries.
- `build_low_agent_review_plan` for reviewer guidance plus caller-supplied changed files or per-agent change sets.
- `snapshot_agent_files` plus `detect_agent_file_changes` for existing caller-supplied files; this hashes files through `app.io.mod`.
- `discover_agent_vcs_changes` for `jj diff --name-only` changed-file discovery through `app.io.mod.process_run`.
- `launch_agent_team` for starting a caller-supplied list of single-agent requests and returning per-agent process records.
- `build_claude_advisor_plan` for Claude advisor prompts.
- `build_codex_goal_plan` for Codex goal prompts.

This surface does not install plugins, discover MCP servers, watch VCS state continuously, persist team supervision, or provide a live chat bus. Callers pass capabilities, file paths, and team transcript entries explicitly, then hand the resulting prompt/argv to existing provider wrappers.

Default verification:

```bash
bin/release/simple test test/01_unit/app/llm_caret/agent_plan_spec.spl --mode=interpreter
bin/release/simple check src/app/llm_caret/agent_plan.spl
```
