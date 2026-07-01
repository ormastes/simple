# Feature: llm_caret_agent_teams

## Raw Request
$sp_dev improve llm caret, with mdsoc+ arch, design first check claude arch/design analysis documents and research first. add featuee, 1. agent launch with agent md and skill and task desc. 2. launch agent teams 3. review feature of low agent works(file changes, file change tracking fwature needed for wach agents). 4. claude advisor feature 5. goal feature of codex. 5. agent team interaction. 6. btw and side feature

## Task Type
feature

## Refined Goal
Add a small LLM Caret agent-planning surface that builds deterministic Claude/Codex launch, team, review, advisor, goal, and interaction requests from agent markdown, skill, task, and file-change inputs.

## Acceptance Criteria
- AC-1: A pure API builds a single-agent launch plan from agent markdown path, skill path, task description, and provider, preserving prompt text and structured argv.
- AC-2: A pure API builds a team launch plan with multiple agent/task pairs and explicit interaction mode text.
- AC-3: A pure API builds low-agent review prompts from tracked changed files and reviewer guidance.
- AC-4: A pure API builds Claude advisor and Codex goal requests without requiring live Claude/Codex binaries.
- AC-5: Requirements, MDSOC architecture, design, agent task, and guide/skill docs identify the supported static-planning scope and excluded live supervisor scope.
- AC-6: Agent launch plans can carry explicit agent, skill, MCP server, and plugin capability lists in the same handoff style as SPipe.
- AC-7: Team interaction plans can render explicit `btw` and `side` transcript entries without a live message bus.
- AC-8: A file snapshot helper records existing caller-supplied file hashes per agent through the app I/O facade.
- AC-9: A minimal team launcher starts a list of single-agent requests and returns per-agent process records without persisting a supervisor.
- AC-10: A VCS helper discovers changed files for an agent through `jj diff --name-only` by default.
- AC-11: Simple MCP/plugin manifest parsing and plugin install argv planning populate agent capability handoffs without executing live installs.
- AC-12: A pure team mailbox routes `btw` and `side` messages with per-agent inbox and channel filters.

## Scope Exclusions
Persistent process registry, live cross-agent transport, plugin install execution, live MCP registry discovery, and background VCS watching are out of this slice. The API accepts changed-file paths/fingerprints, capability lists, manifest text, team mailbox/transcript messages, and team launch request lists supplied by the caller.

## Cooperative Review
Sidecars: N/A for implementation because this slice is two small modules and one unit spec. Merge owner: Codex. Final reviewer: normal/highest-capability Codex review before done. Shared interfaces: `AgentLaunchRequest`, `AgentLaunchPlan`, `AgentCapabilitySet`, `AgentFileFingerprint`, `AgentTeamMessage`, `build_agent_launch_plan`, `build_agent_capability_launch_plan`, `build_agent_team_plan`, `build_btw_side_interaction_plan`, `track_agent_file_changes`, `build_low_agent_review_plan`, `build_agent_change_review_plan`, `build_claude_advisor_plan`, `build_codex_goal_plan`. Manual step helpers: `step("Build a single agent launch plan")`, `step("Build a team plan")`, `step("Build a low-agent review plan")`.

## Phase
impl-verified

## Log
- dev: Created state file with 5 acceptance criteria.

## Architecture

### Module Plan
| Module | Path | Role | New/Modified |
|---|---|---|---|
| agent_plan | `src/app/llm_caret/agent_plan.spl` | Pure static agent/team/review/advisor/goal planning | New |
| agent_files | `src/app/llm_caret/agent_files.spl` | Existing-file hash snapshots and diff handoff | New |
| agent_vcs | `src/app/llm_caret/agent_vcs.spl` | VCS changed-file discovery through process facade | New |
| agent_runtime | `src/app/llm_caret/agent_runtime.spl` | Minimal process facade for executable single-agent plans | New |
| agent_discovery | `src/app/llm_caret/agent_discovery.spl` | Pure MCP/plugin manifest parsing and install argv planning | New |
| agent_mailbox | `src/app/llm_caret/agent_mailbox.spl` | Pure `btw`/`side` team mailbox routing | New |
| agent_plan_spec | `test/01_unit/app/llm_caret/agent_plan_spec.spl` | Unit evidence for all builders | New |

### Dependency Map
- `agent_plan.spl` -> Simple std text/list primitives only.
- `agent_files.spl` -> `app.io.mod` file facade and `agent_plan.spl` fingerprint/change types.
- `agent_vcs.spl` -> `app.io.mod` process facade and `agent_plan.spl` change type.
- `agent_runtime.spl` -> `app.io.mod` process facade and `agent_plan.spl` plan type.
- `agent_discovery.spl` -> Simple std text/list primitives only.
- `agent_mailbox.spl` -> `agent_plan.spl` message type only.
- Provider wrappers consume prompt/argv outputs later; no reverse dependency.
- No circular dependencies: verified by module shape.

### Decisions
- **D-1:** Static planning plus one process launcher only, because persistent live supervision needs separate lifecycle requirements.
- **D-2:** Caller supplies changed-file fingerprints, because filesystem diff capture belongs to VCS/tooling callers.
- **D-3:** MCP servers and plugins can be explicit capability names or parsed from caller-supplied manifests; live registry discovery and install execution stay out of this slice.
- **D-4:** File snapshots hash only caller-supplied existing paths; VCS-wide discovery is a later lane.
- **D-5:** VCS discovery shells through `app.io.mod.process_run` and defaults to `jj diff --name-only`; background watching is a later lane.
- **D-6:** Team interaction is a pure mailbox/transcript API; live transport and persistence are later lanes.

### Public API
- `AgentLaunchRequest`, `AgentLaunchPlan`, `AgentReviewRequest`, `AgentFileChangeSet`, `AgentFileFingerprint`, `AgentCapabilitySet`, `AgentTeamMessage`
- `build_agent_launch_plan`, `build_agent_capability_launch_plan`, `build_agent_team_plan`, `build_agent_team_interaction_plan`, `build_btw_side_interaction_plan`, `track_agent_file_changes`, `build_low_agent_review_plan`, `build_agent_change_review_plan`, `build_claude_advisor_plan`, `build_codex_goal_plan`
- `AgentProcess`, `AgentTeamProcess`, `agent_command_for_provider`, `launch_agent_plan`, `launch_agent_team`, `summarize_agent_team`, `agent_team_status`, `stop_agent_team`, `agent_process_status`, `stop_agent_process`
- `snapshot_agent_files`, `detect_agent_file_changes`
- `parse_vcs_changed_files`, `discover_agent_vcs_changes`
- `AgentDiscoverySet`, `parse_mcp_manifest`, `parse_plugin_manifest`, `discover_agent_capabilities`, `build_plugin_install_args`
- `AgentTeamMailbox`, `new_agent_team_mailbox`, `post_agent_team_message`, `post_btw_message`, `post_side_message`, `agent_team_inbox`, `agent_team_channel`, `agent_team_transcript`

### Requirement Coverage
- REQ-001 -> `build_agent_launch_plan`
- REQ-002 -> `build_agent_team_plan`
- REQ-003 -> `build_low_agent_review_plan`
- REQ-004 -> `build_agent_change_review_plan`, `build_claude_advisor_plan`, `build_codex_goal_plan`
- REQ-005 -> unit-only pure spec
- REQ-006 -> `AgentCapabilitySet`, `build_agent_capability_launch_plan`
- REQ-007 -> `AgentTeamMessage`, `build_btw_side_interaction_plan`
- REQ-008 -> `snapshot_agent_files`, `detect_agent_file_changes`
- REQ-009 -> `launch_agent_team`, `summarize_agent_team`
- REQ-010 -> `parse_vcs_changed_files`, `discover_agent_vcs_changes`
- REQ-011 -> `parse_mcp_manifest`, `parse_plugin_manifest`, `discover_agent_capabilities`, `build_plugin_install_args`
- REQ-012 -> `AgentTeamMailbox`, `post_btw_message`, `post_side_message`, `agent_team_inbox`, `agent_team_channel`

<!-- sdn-diagram:id=llm-caret-agent-plan-state -->
```sdn
component "Caller" -> "agent_plan" : request fields
component "agent_plan" -> "Provider wrapper" : prompt + argv
```

## Implementation Evidence

- `bin/release/simple test test/01_unit/app/llm_caret/agent_plan_spec.spl --mode=interpreter` PASS, 15 tests.
- `bin/release/simple test test/01_unit/app/llm_caret/agent_mailbox_spec.spl --mode=interpreter` PASS, 2 tests.
- `bin/release/simple check src/app/llm_caret/agent_plan.spl` PASS.
- `bin/release/simple check src/app/llm_caret/agent_files.spl` PASS.
- `bin/release/simple check src/app/llm_caret/agent_vcs.spl` PASS.
- `bin/release/simple check src/app/llm_caret/agent_runtime.spl` PASS.
- `bin/release/simple check src/app/llm_caret/agent_discovery.spl` PASS.
- `bin/release/simple check src/app/llm_caret/agent_mailbox.spl` PASS.
- `bin/release/simple spipe-docgen test/01_unit/app/llm_caret/agent_plan_spec.spl --output doc/06_spec --no-index` PASS, 0 stubs.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` PASS.

- impl: Added static agent planning API, spec, guide, and skill references.
