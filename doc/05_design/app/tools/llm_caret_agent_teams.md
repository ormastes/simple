# LLM Caret Agent Teams - Detail Design

Date: 2026-07-01

## Data

`AgentLaunchRequest` stores provider, agent markdown path, skill path, task,
model, session id, and extra args. `AgentLaunchPlan` stores provider, mode,
prompt, argv, and summary. `AgentCapabilitySet` stores explicit agent files,
skill files, MCP servers, and plugins. `AgentReviewRequest` stores reviewer,
changed files, and guidance. `AgentFileFingerprint` stores caller-supplied
before/after fingerprints by agent and file path. `AgentProcess` stores the
minimal launcher PID/status result. `AgentTeamProcess` stores a non-persistent
set of per-agent process records. `AgentVcsChangeResult` stores the result of a
VCS changed-file discovery command. `AgentDiscoverySet` stores parsed MCP
server and plugin names. `AgentTeamMessage` stores explicit team transcript
entries. `AgentTeamMailbox` stores an in-memory team transcript. TUI renderers
return plain text for operator/system-test visibility.

## Builders

- Single-agent launch: builds one prompt with agent, skill, and task fields.
- Capability launch: adds SPipe-like agent, skill, MCP, and plugin lists.
- Team launch: concatenates member launch prompts and records interaction mode.
- Team interaction: renders caller-supplied `btw` and `side` transcript entries.
- Low-agent review: lists changed files supplied by caller; no filesystem scan.
- File-change tracking: compares caller-supplied before/after fingerprints.
- File snapshot: records hashes for existing caller-supplied file paths only.
- VCS discovery: runs `jj diff --name-only` by default and parses unique paths.
- Capability discovery: parses simple JSON/YAML-like manifest names and builds
  plugin install argv lists without running an installer.
- Team mailbox: appends `btw`/`side` messages and returns per-agent inbox,
  channel-filtered, or full transcript views.
- TUI rendering: converts capability handoffs, team mailboxes, and filtered
  inboxes into deterministic text sections.
- Claude advisor: returns provider `claude_cli`, mode `advisor`.
- Codex goal: returns provider `codex`, mode `goal`.
- Runtime launcher: resolves `claude`, `codex`, or `opencode` command names and
  spawns a single already-built plan through `app.io.mod`.
- Team launcher: builds each single-agent plan, launches it, and returns one
  in-memory summary; it does not persist or supervise after the call.

## Errors

This slice does not return `Result`; empty fields stay visible in deterministic
prompt text so callers/tests can catch missing configuration.

## Verification

`test/01_unit/app/llm_caret/agent_plan_spec.spl` covers builders, fingerprint
tracking, manifest parsing, install argv planning, and provider command
resolution with pure assertions. `agent_mailbox_spec.spl` covers `btw`/`side`
message routing. `test/03_system/app/llm_caret/feature/llm_caret_agent_tui_handoff_spec.spl`
covers TUI-visible handoff and team-message output. Persistent live team
supervisors, cancellation policy, plugin install execution, MCP registry
discovery, live message buses, and background VCS watchers need later specs.
