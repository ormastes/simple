<!-- codex-design -->
# Agent Tasks — KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-04-15

## Goal

Build a Simple-native assistant architecture where:

- `simple mcp` is useful by itself as the assistant control plane
- `llm dashboard` is useful by itself as the assistant operations view
- together they form a live, inspectable, controllable system

## Why This Plan

- Keeps autonomy local-first and explicit.
- Reuses existing MCP, dashboard, SDN, and crash-containment work.
- Avoids coupling the dashboard to implementation-only state.
- Lets parallel agents work on mostly disjoint slices.

## Phase Order

1. Define assistant core contracts and persistence model.
2. Implement standalone `simple mcp` assistant session features.
3. Implement standalone `llm dashboard` observation features.
4. Add the live synergy bridge between them.
5. Verify fault isolation, visibility, and degraded-mode behavior.

## Agent Breakdown

### Agent 1: Assistant Core and Data Contracts

Own:

- assistant session schema
- tick record schema
- signal/event schema
- brief/digest schema
- retention and summarization rules
- standalone vs synergy contract

Deliverables:

- architecture/design docs for core records and lifecycle
- SDN/file layout proposal
- invariants for pause/resume/ack/brief/spawn

Do not own:

- UI rendering
- final dashboard views
- transport-specific implementation details

### Agent 2: `simple mcp` Control Plane

Own:

- assistant lifecycle commands/tools
- session list/detail/timeline APIs
- tick scheduler and wake-reason handling
- signal injection API
- brief generation API
- child-agent spawn/delegate control path

Deliverables:

- MCP tool/resource/prompt surface
- local CLI fallback for status/brief
- standalone operation without dashboard present

Do not own:

- dashboard rendering
- long-term dashboard DB presentation

### Agent 3: `llm dashboard` Operations Surface

Own:

- session overview panels
- timeline/event views
- task/subagent tree views
- notification/blocker panes
- resource/failure/status indicators

Deliverables:

- collectors for assistant/session data
- CLI/web view updates
- standalone replay/import mode when no live MCP source exists

Do not own:

- scheduler internals
- assistant control semantics beyond invoking documented actions

### Agent 4: Synergy Bridge

Own:

- live stream or polling bridge from assistant state into dashboard collectors
- dashboard-to-MCP control actions
- compatibility logic when only one side is installed
- cache/invalidation strategy for live views

Deliverables:

- bridge contract
- failure-handling rules
- latency and stale-data targets

Do not own:

- raw collector UI rendering
- base assistant state machine

### Agent 5: Safety, Budgets, and Recovery

Own:

- process/resource budget propagation
- worker restart semantics
- structured crash telemetry
- timeout/memory thresholds
- degraded-mode behavior after bridge or worker failure

Deliverables:

- test matrix for crash, timeout, disconnect, and stale-state cases
- policy defaults for hosted vs heavy workloads

Do not own:

- feature UI polish
- non-safety product naming

### Agent 6: Verification and Docs

Own:

- system test plan
- requirement traceability
- spec updates
- operator docs and examples
- README / guide integration after implementation stabilizes

Deliverables:

- tests for standalone `simple mcp`
- tests for standalone dashboard replay/import
- tests for combined live mode

## Coordination Rules

- Do not couple dashboard rendering to undocumented in-memory structures; use explicit records/contracts.
- Do not make dashboard live mode mandatory for the assistant core.
- Do not make MCP availability mandatory for dashboard replay/import mode.
- Every background action must produce inspectable state, not silent side effects.
- Every spawned child task must have a parent session ID, objective, status, and terminal summary.
- Every live bridge path must define cache invalidation and stale-view behavior.
- Every resource-consuming worker must carry explicit timeout and memory policy.

## Acceptance Bar

The feature family is ready for implementation review when:

1. `simple mcp` can run and inspect assistant sessions without the dashboard.
2. `llm dashboard` can inspect assistant data without a live MCP dependency.
3. Combined mode adds live controls and richer visibility without becoming a hard dependency.
4. Spawned child-agent work is visible as structured state, not only as logs.
5. Tick, signal, and notification paths are separately testable.
6. Crash/restart behavior preserves enough structured evidence for diagnosis.
7. Dashboard assistant replay path must render without runtime coercion failures on real transcript data.

## Suggested First Implementation Slice

1. Session schema + on-disk state.
2. Tick scheduler with manual signal injection.
3. MCP tools: start, pause, resume, brief, list, timeline.
4. Dashboard collectors: sessions, ticks, signals, child tasks.
5. One compact dashboard view for session health and recent actions.
6. Verification for standalone and combined degraded modes.

Current validation note:

- `simple dashboard status` works after the dashboard loader/runtime fixes landed.
- `simple dashboard assistant` replay-data coercion bug was fixed on 2026-04-15; see [bug_report_dashboard_assistant_cast_runtime_2026-04-15.md](/home/ormastes/dev/pub/simple/doc/08_tracking/bug/bug_report_dashboard_assistant_cast_runtime_2026-04-15.md) for the resolution and the remaining `bug-resolve` tracking utility blocker.
- Generic `n as i64` and `"{n as i64}"` semantics are covered by [cast_numeric_parity_spec.spl](/home/ormastes/dev/pub/simple/test/unit/compiler/interpreter/cast_numeric_parity_spec.spl), so the remaining defect should be treated as a collector/replay-path bug, not a language-level cast bug.

Open follow-up TODO:

- The MCP assistant surface is now backed by the extracted store/query modules under `src/app/mcp/assistant/**`, and `assistant_start`/dashboard replay are working end-to-end.
- The remaining work is follow-up product work, not a confirmed defect:
  - move the rest of the assistant/task lifecycle onto the extracted core API
  - route child-task creation and task-tree state through the shared core
  - continue dashboard live-bridge/session-tree integration on top of the extracted assistant core
- Tracked in [doc/08_tracking/todo/kairos_like_simple_mcp_llm_dashboard_follow_up_2026-04-15.md](/home/ormastes/dev/pub/simple/doc/08_tracking/todo/kairos_like_simple_mcp_llm_dashboard_follow_up_2026-04-15.md)
