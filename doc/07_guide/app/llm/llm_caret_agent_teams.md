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
- `parse_mcp_manifest`, `parse_plugin_manifest`, `discover_agent_capabilities`, and `build_plugin_install_args` for manifest-backed MCP/plugin handoff setup without live installs.
- `new_agent_team_mailbox`, `post_btw_message`, `post_side_message`, `agent_team_inbox`, `agent_team_channel`, and `agent_team_transcript` for pure team message exchange.
- `render_agent_handoff_tui`, `render_agent_mailbox_tui`, and `render_agent_messages_tui` for TUI-readable operator/system-test views.
- `build_agent_tmux_embed` and `render_agent_tmux_tui` for embedded tmux-style process panes with caller-supplied CPU/memory usage.
- `launch_agent_team` for starting a caller-supplied list of single-agent requests and returning per-agent process records.
- `build_claude_advisor_plan` for Claude advisor prompts.
- `build_codex_goal_plan` for Codex goal prompts.

## SPipe Capability Surface

Use the same four capability groups in SPipe state, prompts, TUI handoffs,
generated manuals, and review notes:

- `agent_paths`: agent instruction files such as `.claude/agents/spipe/dev.md`.
- `skill_paths`: skill files such as `.codex/skills/sp_dev/SKILL.md`.
- `mcp_servers`: MCP server names or package identifiers such as `simple-mcp`.
- `plugins`: plugin identifiers such as `ponytail`.

`AgentCapabilitySet` is the canonical in-code shape. Do not invent parallel
names like `tool_agents`, `skill_agents`, `mcp_tools`, or `plugin_caps` in new
SPipe docs or SSpec helpers. Capability discovery is intentionally bounded:
`parse_mcp_manifest` and `parse_plugin_manifest` extract simple names from
caller-supplied manifests, while installs and live registry lookup remain
separate verified lanes.

This surface does not execute plugin installs, query a live MCP registry, watch VCS state continuously, persist team supervision, or provide a live chat bus. Callers pass capabilities, manifests, file paths, and team mailbox/transcript entries explicitly, then hand the resulting prompt/argv to existing provider wrappers.

Default verification:

```bash
bin/release/simple test test/01_unit/app/llm_caret/agent_plan_spec.spl --mode=interpreter
bin/release/simple test test/01_unit/app/llm_caret/agent_mailbox_spec.spl --mode=interpreter
bin/release/simple test test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl --native
bin/release/simple test test/03_system/app/llm_caret/feature/llm_caret_embedded_tmux_tui_spec.spl --mode=interpreter
bin/release/simple check src/app/llm_caret/agent_plan.spl
bin/release/simple check src/app/llm_caret/agent_discovery.spl
bin/release/simple check src/app/llm_caret/agent_mailbox.spl
bin/release/simple check src/app/llm_caret/agent_tui.spl
bin/release/simple check src/app/llm_caret/agent_tmux.spl
```
