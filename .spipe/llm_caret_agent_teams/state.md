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

## Scope Exclusions
Persistent process registry, cross-agent chat bus, plugin install, MCP discovery, and filesystem diff capture are out of this slice. The API accepts changed-file fingerprints and capability lists supplied by the caller.

## Cooperative Review
Sidecars: N/A for implementation because this slice is two small modules and one unit spec. Merge owner: Codex. Final reviewer: normal/highest-capability Codex review before done. Shared interfaces: `AgentLaunchRequest`, `AgentLaunchPlan`, `AgentCapabilitySet`, `AgentFileFingerprint`, `build_agent_launch_plan`, `build_agent_capability_launch_plan`, `build_agent_team_plan`, `track_agent_file_changes`, `build_low_agent_review_plan`, `build_agent_change_review_plan`, `build_claude_advisor_plan`, `build_codex_goal_plan`. Manual step helpers: `step("Build a single agent launch plan")`, `step("Build a team plan")`, `step("Build a low-agent review plan")`.

## Phase
impl-verified

## Log
- dev: Created state file with 5 acceptance criteria.

## Architecture

### Module Plan
| Module | Path | Role | New/Modified |
|---|---|---|---|
| agent_plan | `src/app/llm_caret/agent_plan.spl` | Pure static agent/team/review/advisor/goal planning | New |
| agent_runtime | `src/app/llm_caret/agent_runtime.spl` | Minimal process facade for executable single-agent plans | New |
| agent_plan_spec | `test/01_unit/app/llm_caret/agent_plan_spec.spl` | Unit evidence for all builders | New |

### Dependency Map
- `agent_plan.spl` -> Simple std text/list primitives only.
- `agent_runtime.spl` -> `app.io.mod` process facade and `agent_plan.spl` plan type.
- Provider wrappers consume prompt/argv outputs later; no reverse dependency.
- No circular dependencies: verified by module shape.

### Decisions
- **D-1:** Static planning plus one process launcher only, because persistent live supervision needs separate lifecycle requirements.
- **D-2:** Caller supplies changed-file fingerprints, because filesystem diff capture belongs to VCS/tooling callers.
- **D-3:** MCP servers and plugins are explicit capability names, not discovered or installed here.

### Public API
- `AgentLaunchRequest`, `AgentLaunchPlan`, `AgentReviewRequest`, `AgentFileChangeSet`, `AgentFileFingerprint`, `AgentCapabilitySet`
- `build_agent_launch_plan`, `build_agent_capability_launch_plan`, `build_agent_team_plan`, `track_agent_file_changes`, `build_low_agent_review_plan`, `build_agent_change_review_plan`, `build_claude_advisor_plan`, `build_codex_goal_plan`
- `AgentProcess`, `agent_command_for_provider`, `launch_agent_plan`, `agent_process_status`, `stop_agent_process`

### Requirement Coverage
- REQ-001 -> `build_agent_launch_plan`
- REQ-002 -> `build_agent_team_plan`
- REQ-003 -> `build_low_agent_review_plan`
- REQ-004 -> `build_agent_change_review_plan`, `build_claude_advisor_plan`, `build_codex_goal_plan`
- REQ-005 -> unit-only pure spec
- REQ-006 -> `AgentCapabilitySet`, `build_agent_capability_launch_plan`

<!-- sdn-diagram:id=llm-caret-agent-plan-state -->
```sdn
component "Caller" -> "agent_plan" : request fields
component "agent_plan" -> "Provider wrapper" : prompt + argv
```

## Implementation Evidence

- `bin/release/simple test test/01_unit/app/llm_caret/agent_plan_spec.spl --mode=interpreter` PASS, 9 tests.
- `bin/release/simple check src/app/llm_caret/agent_plan.spl` PASS.
- `bin/release/simple check src/app/llm_caret/agent_runtime.spl` PASS.
- `bin/release/simple spipe-docgen test/01_unit/app/llm_caret/agent_plan_spec.spl --output doc/06_spec --no-index` PASS, 0 stubs.
- `sh scripts/audit/direct-env-runtime-guard.shs --working` PASS.

- impl: Added static agent planning API, spec, guide, and skill references.
