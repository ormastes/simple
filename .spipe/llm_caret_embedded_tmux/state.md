# Feature: llm_caret_embedded_tmux

## Raw Request
$sp_dev embedding tmux, separate processes and cpu/memor usages. simple tmx impl exist reuse logic. check its tui.

## Acceptance Criteria

- AC-1: Reuse the existing Simple tmux session/pane model.
- AC-2: Render separate LLM Caret agent processes as separate tmux panes.
- AC-3: Show PID, status, CPU percent, and memory MB in a TUI-readable view.
- AC-4: Keep process usage snapshots caller-supplied; do not add direct runtime or shell sampling in LLM Caret.
- AC-5: Add executable SSpec coverage and generated manual docs.
- AC-6: Keep SPipe agent/skill/MCP/plugin handoff support homogeneous with
  LLM Caret by using `agent_paths`, `skill_paths`, `mcp_servers`, and
  `plugins` in guides, skills, agent prompts, and command prompts.

## Scope Exclusions

Live PTY attachment, host tmux execution, keyboard routing, full tmux parity,
and direct process sampling are deferred.

## Evidence

- `bin/release/simple check src/app/llm_caret/agent_tmux.spl` PASS.
- `bin/release/simple test test/01_unit/tools/desktop/tmux_session_model_spec.spl --mode=interpreter` PASS, 4 tests.
- `bin/release/simple test test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl --mode=interpreter --clean` exited 0 with summary `Passed: 2`, `Failed: 0`; the artifact `result.json` records `status: "passed"` and also carries the runner note `error: "Process exited with code 1"`.
- `bin/release/simple spipe-docgen test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl --output doc/06_spec --no-index` PASS, 1 complete doc, 0 stubs.
- `bin/release/simple test test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl --native` PASS, 3 tests.
- `bin/release/simple check src/app/llm_caret/agent_plan.spl` PASS.
- `bin/release/simple check src/app/llm_caret/agent_discovery.spl` PASS.
- `find doc/06_spec -name '*_spec.spl' | wc -l` printed `0`.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` PASS.
- `sh scripts/audit/direct-env-runtime-guard.shs --staged` PASS.

## Process Docs

- `doc/07_guide/app/llm/llm_caret_agent_teams.md` now documents the canonical
  SPipe capability surface.
- `.codex/skills/sp_dev/SKILL.md`, `.agents/skills/impl/SKILL.md`,
  `.claude/skills/spipe.md`, `.claude/agents/spipe/dev.md`,
  `.claude/agents/spipe/verify.md`, `.gemini/commands/impl.toml`,
  `.gemini/commands/sp_dev.toml`, and `.gemini/commands/verify.toml` now route
  agent, skill, MCP, and plugin handoff through the same four field names.
