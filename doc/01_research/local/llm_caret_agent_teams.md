# LLM Caret Agent Teams - Local Research

Date: 2026-07-01

## Existing Code

- `src/app/llm_caret/claude_cli.spl` already builds Claude CLI argv and parses JSON output.
- `src/app/llm_caret/opencode_cli.spl` already builds OpenCode argv and PID helpers.
- `src/app/llm_caret/mod.spl` exposes the chat facade, but no `simple llm` command, goal command, advisor command, or agent-team supervisor exists.
- Unit specs under `test/01_unit/app/llm_caret/` mostly test pure builders inline to avoid live CLI dependencies.

## Existing Process Docs Checked

- `.claude/agents/spipe/dev.md` requires a lane state file with acceptance criteria and cooperative review.
- `.claude/agents/spipe/arch.md` requires module paths, dependency map, public API, and one SDN diagram.
- `.claude/skills/design.md` requires design docs and agent-task docs before implementation.
- `doc/07_guide/app/llm/llm_cooperative_dev_phase.md` documents multi-LLM phase ownership and sidecar review expectations.

## Gap

LLM Caret can call providers, but it lacks a stable data contract for preparing
agent launches, team launches, low-agent review requests, Claude advisor prompts,
and Codex goal prompts. Adding a pure planning module is enough for callers to
use existing provider wrappers without introducing a process supervisor.
