<!-- codex-research -->
# KAIROS-Like Simple MCP + LLM Dashboard — Local Research

Date: 2026-04-15
Scope: `simple mcp`, `simple dashboard`, and shared runtime seams for a persistent/proactive assistant layer that is useful standalone in each surface and stronger when both are installed together.

## Goal

Identify what already exists in this repo that can support a KAIROS-like feature set:

- persistent session state
- background or low-priority work
- proactive wakeups
- external event intake
- dashboard visibility into agent state
- safe standalone behavior in either `simple mcp` or `llm dashboard`

## Existing Local Building Blocks

### 1. `simple mcp` already has a viable control plane shell

Relevant evidence:

- `src/app/mcp/main.spl`
- `doc/01_research/local/mcp_feature_analysis_2026-02-05.md`
- `README.md`

Observed local state:

- The MCP server already exposes JSON-RPC over stdio and has a modular dispatch split.
- The local MCP research doc records a table-driven architecture with extension seams for protocol, tool registry, query tools, task tools, and daemon-related handlers.
- The repo already treats MCP as a first-class integration surface, not an afterthought.

Implication:

- A KAIROS-like feature should not start as a separate unrelated server.
- The right shape is an additive MCP capability layer around session state, scheduling, signals/events, summaries, and assistant control APIs.

### 2. The dashboard already has a metrics/state substrate

Relevant evidence:

- `src/app/dashboard/main.spl`
- `src/app/dashboard/dashboard_collectors.spl`
- `src/app/dashboard/dashboard_alerts_and_queries.spl`
- `src/app/dashboard.render/*`
- `src/app/dashboard.views/status.spl`
- `doc/10_metrics/dashboard/README.md`
- `doc/spec/dashboard_render_spec.md`
- `doc/spec/tmux_rest_api_spec.md`

Observed local state:

- The dashboard already collects structured project/test/todo/coverage/verification/build data into SDN-backed stores.
- The dashboard already supports CLI views, shared HTML rendering, and a web/TMUX-facing API surface.
- The metrics README already documents cache invalidation, snapshots, collection cadence, and reuse of existing data sources.

Implication:

- The dashboard does not need a brand-new UI stack to support a KAIROS-like mode.
- It needs new agent/session-specific collectors, views, and timelines layered into the current summary/query/export surfaces.

### 3. Crash containment and worker isolation work already exists

Relevant evidence:

- `doc/01_research/local/dashboard_crash_containment_framework.md`
- `src/lib/nogc_sync_mut/io/process_limit_enforcer.spl`
- `src/lib/nogc_sync_mut/io/process_ops.spl`
- `src/compiler_rust/compiler/src/watchdog.rs`

Observed local state:

- The repo already has process-level caps, timeout/memory/fd/proc enforcement, and worker restart thinking.
- The local crash-containment research explicitly calls out heavy hosted workloads, supervised workers, and resource-budget propagation.
- The current gap is not “no safety model”; it is incomplete propagation, stale system-test pathing, and limited structured crash telemetry.

Implication:

- A proactive assistant loop can be hosted safely if it uses the existing supervised-worker pattern.
- The implementation must carry explicit runtime budgets and structured failure records from day one.

### 4. Background-loop patterns already exist in adjacent tooling

Relevant evidence:

- `src/app/build/watch.smf`
- references in MCP split modules summarized by `doc/01_research/local/mcp_feature_analysis_2026-02-05.md`
- `doc/report/unique_features.md`

Observed local state:

- The repo already uses watch/daemon style behavior for build-oriented flows.
- MCP research references task/test-daemon-oriented modules and background-task seams.
- The product posture already tolerates long-lived tooling processes when they are resource-bounded and operationally clear.

Implication:

- A periodic tick loop is compatible with repo direction.
- The implementation should reuse existing watch/daemon policies rather than inventing a hidden agent loop with bespoke lifecycle rules.

### 5. There is already a repo-level concept of LLM UI and widget surfaces

Relevant evidence:

- `src/os/capsule.sdn` exports `mcp_os_server_start` and `llm_widget_eval`
- `doc/01_research/local/dashboard_ui_research.md`

Observed local state:

- The repo is already exploring LLM-facing dashboards and companion views.
- Prior research already identifies task monitoring, subagent tracing, plugin panels, and companion layouts as relevant patterns.

Implication:

- A KAIROS-like dashboard should emphasize session status, agent tree, pending signals, recent actions, memory/digest state, and approval bottlenecks.
- This is aligned with existing LLM dashboard direction rather than a new product branch.

## Current Gaps

### Gap 1. No first-class persistent assistant session model in Simple

The repo has sessions in multiple domains, but no unified assistant-session abstraction with:

- session identity
- current objective
- last tick time
- wake reason
- pending external signals
- deferred actions
- compact brief state
- durable memory/digest state

### Gap 2. No explicit proactive scheduler for agent work

There are watch/daemon patterns, but no dedicated assistant scheduler that can distinguish:

- periodic tick
- user nudge
- external event push
- resume after crash
- debounce/coalesce window
- low-priority vs urgent queue

### Gap 3. No dashboard model for agent execution traces

Current dashboard data is project-centric. It is not yet agent-centric. Missing data families include:

- assistant sessions
- ticks
- signals/events
- actions taken vs suppressed
- spawned agent/subtask graph
- notification delivery log
- memory/digest checkpoints

### Gap 4. No MCP contract for “assistant control” yet

The current MCP surface is useful for reading, searching, and task tooling, but it does not yet expose a clear assistant control API such as:

- `assistant.start`
- `assistant.pause`
- `assistant.brief`
- `assistant.subscribe`
- `assistant.push_signal`
- `assistant.list_sessions`
- `assistant.get_timeline`

### Gap 5. Standalone/synergy behavior is not defined

The user request requires:

- `simple mcp` alone must still be useful
- `llm dashboard` alone must still be useful
- together they must produce a stronger combined workflow

This separation is not encoded today.

## Recommended Local Product Split

### Standalone: `simple mcp`

Own:

- assistant session model
- assistant state store
- tick scheduler
- event/signal intake
- spawn/delegate orchestration
- compact brief generation
- notification decisioning
- MCP control tools/resources/prompts

Without dashboard installed, this should still work via:

- MCP tools
- CLI status/brief commands
- plain JSON/SDN logs

### Standalone: `llm dashboard`

Own:

- visualization of sessions, events, tasks, blockers, resource budgets, and summaries
- operator controls for pause/resume/ack/retry/filter
- comparative views across multiple agent sessions
- timeline and inbox surfaces

Without `simple mcp`, this should still be able to:

- inspect imported logs/snapshots
- visualize local dashboard DB data
- present static/replayed assistant runs

### Synergy: `simple mcp` + `llm dashboard`

Together they should add:

- live session streaming into dashboard collectors
- clickable agent tree and event timeline
- control-plane actions from dashboard routed back through MCP
- dashboard-originated subscription and filtering rules
- “brief mode” summaries grounded in the full session/event state

## Suggested Initial Feature Shape

Phase-1-worthy local scope:

1. Assistant session record and on-disk state.
2. Tick scheduler with explicit wake reasons and rate limits.
3. Signal intake API for external pushes and internal reminders.
4. Brief/digest generator over recent session activity.
5. MCP tools for control and inspection.
6. Dashboard collectors and views for session/timeline/state.

Deferred until after core path is stable:

- autonomous code mutation on unsolicited ticks
- cross-repo multi-session orchestration
- speculative multi-agent swarms by default
- deep long-term memory compaction beyond bounded digests

## Local Risks

1. A hidden autonomous loop will conflict with the repo’s explicit safety posture unless all background work is visible and resource-bounded.
2. Agent/session telemetry can bloat SDN stores unless retention and summarization are designed up front.
3. Dashboard polling can become the bottleneck if the live view re-reads full stores instead of consuming append-oriented deltas.
4. Standalone dashboard mode can become fake if it depends on live MCP-only state instead of documented import/snapshot paths.

## Conclusion

The repo already has most of the primitives needed for a KAIROS-like feature family:

- MCP control surface
- dashboard data/rendering surface
- watch/daemon patterns
- crash-containment policies

What is missing is the cohesive assistant-session architecture that ties them together. The correct direction is not “copy leaked KAIROS literally.” The correct direction is:

- implement a first-class assistant/session core in `simple mcp`
- expose an observable operator surface in `llm dashboard`
- define a strict standalone contract for each
- add a live synergy layer when both are present
