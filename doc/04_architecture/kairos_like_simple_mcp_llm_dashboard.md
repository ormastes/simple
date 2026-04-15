<!-- codex-design -->
# Architecture: KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-04-15

## Decision

Adopt a three-plane architecture:

1. **Assistant Core Plane** in `simple mcp`
2. **Operations Plane** in `llm dashboard`
3. **Synergy Bridge Plane** for live attachment and control routing

The assistant core owns authoritative state. The dashboard owns operator visibility. The bridge owns live synchronization and control relaying, but it is never the source of truth.

## Why This Architecture

- Matches the selected broad feature scope without forcing hard runtime coupling.
- Reuses existing MCP dispatch seams, dashboard collectors/renderers, and crash-containment policies.
- Preserves standalone usefulness of each product.
- Keeps background autonomy explicit, inspectable, and bounded.

## Architecture Layers

### Layer 1: Assistant Core (`simple mcp`)

Owns:

- session registry
- tick scheduler
- signal inbox
- child-agent manager
- digest generator
- notification decision engine
- persisted assistant records

Primary outputs:

- MCP tools/resources/prompts
- CLI summary/status access
- append-oriented durable records

### Layer 2: Operations Plane (`llm dashboard`)

Owns:

- session overview views
- timeline/event panels
- task tree panels
- failure/blocker/notification views
- replay/import mode from persisted records

Primary inputs:

- snapshot records
- imported timelines
- live bridge deltas

### Layer 3: Synergy Bridge

Owns:

- live stream or polling delta sync from assistant records into dashboard collectors
- freshness markers
- operator action routing back to assistant MCP controls
- degraded-mode detection

## Core Data Model

### AssistantSession

Fields:

- `session_id`
- `parent_session_id?`
- `mode`
- `objective`
- `status`
- `policy`
- `created_at`
- `updated_at`
- `last_tick_at?`
- `last_wake_reason?`
- `digest_checkpoint_id?`

### SessionEvent

Fields:

- `event_id`
- `session_id`
- `event_type`
- `wake_reason`
- `summary`
- `severity`
- `created_at`
- `source`
- `correlation_id?`

### ChildTask

Fields:

- `task_id`
- `session_id`
- `parent_task_id?`
- `objective`
- `owner_kind`
- `status`
- `resource_policy`
- `started_at`
- `ended_at?`
- `result_summary?`

### DigestCheckpoint

Fields:

- `checkpoint_id`
- `session_id`
- `time_window`
- `summary`
- `blockers`
- `follow_ups`
- `retained_facts`

### NotificationRecord

Fields:

- `notification_id`
- `session_id`
- `trigger_event_id`
- `channel`
- `decision`
- `suppression_reason?`
- `delivery_status`

## Lifecycle Flow

### Normal Flow

1. Assistant session starts in the core plane.
2. Scheduler tick or external signal wakes the session.
3. Core decides act/no-act and records a timeline event.
4. If needed, the core spawns bounded child tasks.
5. Child results merge into the session timeline and digest state.
6. Bridge publishes deltas to dashboard collectors.
7. Dashboard renders current session, tasks, blockers, and notifications.

### Replay / Standalone Dashboard Flow

1. Dashboard loads persisted assistant records or snapshots.
2. Dashboard reconstructs session, event, task, and digest views.
3. No live actions are available unless the bridge and assistant core are attached.

## Spawn-Agent Architecture

### Parent/Child Contract

Every child task must have:

- a parent session ID
- a concrete objective
- a bounded resource policy
- a terminal status
- a merge-back summary

### Delegation Policy

Use child-agent spawn only when:

- the work is separable
- the parent can continue meaningfully
- the write/read scope is explicit

Avoid delegation when:

- the next parent action is blocked on the result
- the task is too coupled to split safely
- the cost of orchestration exceeds the value

### Visibility Policy

Spawned tasks must be visible in both:

- MCP inspection APIs
- dashboard task-tree and timeline views

## Startup Path

The startup path must:

1. load assistant configuration
2. initialize the session registry and persisted stores
3. initialize scheduler state without replaying the entire history into hot memory
4. start live bridge hooks only if the dashboard integration is configured

Risk to avoid:

- full-store reconstruction on every startup

## Hot Paths

Performance-sensitive hot paths:

- session list/detail/brief
- tick dispatch
- signal enqueue
- child-task status updates
- dashboard live delta refresh

Hot-path rules:

- append-oriented writes
- cached summary views
- no per-request subprocesses without justification
- no repeated full-store scans in the live loop

## Cache and Invalidation Strategy

Cache:

- latest session summaries
- active task-tree projections
- latest digest checkpoint pointers
- dashboard overview aggregates

Invalidate on:

- session state transition
- new event append
- child-task status change
- digest checkpoint creation
- bridge disconnect/reconnect

## Fault Isolation

The assistant core, live bridge, and heavy child work must be isolated enough that:

- a bridge failure does not corrupt assistant state
- a child-agent failure does not kill the parent session
- notification delivery failure does not stall the scheduler

Use existing crash-containment policy:

- explicit timeout/memory budgets
- restart with structured evidence
- visible degraded mode instead of silent retries

## MDSOC Notes

This feature is a cross-cutting tooling capsule rather than a language/runtime feature transform. The preferred structure is a virtual capsule spanning:

- `app.mcp.assistant.*`
- `app.dashboard.assistant.*`
- bridge/adapter modules between them

Do not smear assistant logic into dashboard render modules or generic MCP protocol helpers.

## Key Risks

1. Over-coupling the dashboard to live internal state instead of explicit records.
2. Letting digest/memory behavior become vague or unbounded.
3. Hiding autonomy behind silent background work.
4. Replaying too much history in startup or live-refresh hot paths.

## Consequences

This architecture supports the selected broad scope, but it requires disciplined contracts and stronger observability than a narrow MVP. The benefit is that future growth in notifications, multi-session operations, and richer delegation can extend the same core instead of forcing a redesign.
