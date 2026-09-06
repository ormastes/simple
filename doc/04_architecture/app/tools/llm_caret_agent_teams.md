# LLM Caret Agent Teams - MDSOC Architecture

Date: 2026-07-01

## Current State

`src/app/llm_caret` has provider wrappers and chat state, but no shared agent/team request node. Tests prefer pure builders with no live CLI dependency.

## To-Be Layers

| Layer | Path | Visibility |
|---|---|---|
| Common request node | `src/app/llm_caret/agent_plan.spl` | public to LLM Caret callers |
| File snapshot node | `src/app/llm_caret/agent_files.spl` | public helper over app I/O facade |
| VCS discovery node | `src/app/llm_caret/agent_vcs.spl` | public helper over app process facade |
| Capability discovery node | `src/app/llm_caret/agent_discovery.spl` | public pure manifest parser |
| Team mailbox node | `src/app/llm_caret/agent_mailbox.spl` | public pure message queue |
| TUI render node | `src/app/llm_caret/agent_tui.spl` | public pure text renderer |
| Runtime launcher | `src/app/llm_caret/agent_runtime.spl` | public wrapper over process facade |
| Provider wrappers | `src/app/llm_caret/*_cli.spl` | sibling consumers of prompt/argv outputs |
| CLI/app callers | future `src/app/**` | consume only exported planner APIs |

## Encapsulation

- `agent_plan.spl` owns agent/team/review/advisor/goal request structs and deterministic prompt construction.
- `AgentCapabilitySet` owns the SPipe-like explicit agent, skill, MCP server, and plugin handoff lists.
- `AgentTeamMessage` owns deterministic team transcript entries with `btw` and `side` channels supplied by callers.
- `track_agent_file_changes` compares caller-supplied before/after fingerprints by agent.
- `agent_files.spl` snapshots existing paths with `file_exists` and `file_hash_sha256` from `app.io.mod`.
- `agent_vcs.spl` runs `jj diff --name-only` or caller-supplied VCS args through `app.io.mod.process_run`.
- `agent_discovery.spl` parses small MCP/plugin manifest text and builds plugin install argv lists without executing them.
- `agent_mailbox.spl` appends caller-supplied `btw` and `side` messages and filters transcript views by agent or channel.
- `agent_tui.spl` renders capability handoffs and mailbox/inbox messages as TUI-readable text for SSpec and operator review.
- `agent_runtime.spl` spawns already-built single-agent plans and can launch a caller-supplied request list as one non-persistent team result.
- Provider wrappers do not read agent markdown or track files; they only receive prompt/argv from callers.
- File diff capture and live process supervision remain outside this node.

<!-- sdn-diagram:id=llm-caret-agent-plan -->
```sdn
component "Caller" -> "agent_plan.spl" : request fields
component "agent_plan.spl" -> "Claude/Codex/OpenCode wrapper" : prompt + argv
component "Review caller" -> "agent_plan.spl" : changed files + guidance
```

## Public API

- `AgentLaunchRequest`, `AgentLaunchPlan`, `AgentReviewRequest`
- `build_agent_launch_plan(req) -> AgentLaunchPlan`
- `build_agent_capability_launch_plan(req, caps) -> AgentLaunchPlan`
- `build_agent_team_plan(requests, interaction_mode) -> AgentLaunchPlan`
- `build_agent_team_interaction_plan(messages, interaction_mode) -> AgentLaunchPlan`
- `build_btw_side_interaction_plan(messages) -> AgentLaunchPlan`
- `build_low_agent_review_plan(req) -> AgentLaunchPlan`
- `build_claude_advisor_plan(topic, context) -> AgentLaunchPlan`
- `build_codex_goal_plan(objective, context) -> AgentLaunchPlan`
- `snapshot_agent_files(agent_id, paths) -> [AgentFileFingerprint]`
- `detect_agent_file_changes(before, after) -> [AgentFileChangeSet]`
- `discover_agent_vcs_changes(agent_id, vcs_path, args) -> AgentVcsChangeResult`
- `parse_vcs_changed_files(agent_id, stdout) -> AgentFileChangeSet`
- `parse_mcp_manifest(manifest) -> [text]`
- `parse_plugin_manifest(manifest) -> [text]`
- `discover_agent_capabilities(mcp_manifests, plugin_manifests) -> AgentDiscoverySet`
- `build_plugin_install_args(plugin, installer, extra_args) -> [text]`
- `AgentTeamMailbox`, `new_agent_team_mailbox`, `post_btw_message`, `post_side_message`
- `agent_team_inbox(mailbox, agent_id) -> [AgentTeamMessage]`
- `agent_team_channel(mailbox, channel) -> [AgentTeamMessage]`
- `agent_team_transcript(mailbox) -> [AgentTeamMessage]`
- `render_agent_handoff_tui(plan, caps) -> text`
- `render_agent_mailbox_tui(mailbox) -> text`
- `render_agent_messages_tui(messages) -> text`
- `launch_agent_plan(agent_id, plan, claude_path, codex_path, opencode_path) -> AgentProcess`
- `launch_agent_team(team_id, requests, claude_path, codex_path, opencode_path) -> AgentTeamProcess`
- `summarize_agent_team(team_id, processes) -> AgentTeamProcess`

## Matrix

| Raw layer | common request node | public to parent | public to next-layer sibling |
|---|---|---|---|
| LLM Caret planner | `AgentLaunchPlan` | exported structs/functions | prompt/argv only |
| Capability handoff | `AgentCapabilitySet`, `AgentDiscoverySet` | explicit agents/skills/MCP/plugins plus manifest parsing | no live registry or install execution |
| Team transcript | `AgentTeamMessage` | explicit btw/side entries | no live bus |
| Team mailbox | `AgentTeamMailbox` | pure inbox/channel views | no persistence or transport |
| TUI handoff | `agent_tui.spl` text renderers | visible operator text | no curses/full-screen state |
| File snapshots | `AgentFileFingerprint` | existing-file hashes | no VCS scanning |
| VCS discovery | `AgentVcsChangeResult` | changed file list | no background watcher |
| Runtime launcher | `AgentProcess`, `AgentTeamProcess` | PID/status wrapper | no registry or supervisor |
| Provider wrappers | prompt/argv | no private planner state | no direct file tracking |
