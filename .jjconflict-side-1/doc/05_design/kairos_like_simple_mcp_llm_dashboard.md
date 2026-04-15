<!-- codex-design -->
# Detail Design: KAIROS-Like Simple MCP + LLM Dashboard

Date: 2026-04-15

## Module Plan

### `simple mcp` side

Proposed module family:

- `src/app/mcp/assistant/session_store.spl`
- `src/app/mcp/assistant/scheduler.spl`
- `src/app/mcp/assistant/signal_inbox.spl`
- `src/app/mcp/assistant/child_tasks.spl`
- `src/app/mcp/assistant/digest.spl`
- `src/app/mcp/assistant/notifications.spl`
- `src/app/mcp/assistant/tools.spl`

Responsibilities:

- load/store session records
- append events
- evaluate ticks/signals
- create child tasks
- compute briefs/digests
- expose control APIs

### `llm dashboard` side

Proposed module family:

- `src/app/dashboard/assistant_collectors.spl`
- `src/app/dashboard/assistant_queries.spl`
- `src/app/dashboard.views/assistant_status.spl`
- `src/app/dashboard.views/assistant_timeline.spl`
- `src/app/dashboard.views/assistant_tasks.spl`

Responsibilities:

- collect snapshot/live assistant state
- build overview aggregates
- render session/timeline/task views
- support replay/import mode

### bridge side

Proposed module family:

- `src/app/dashboard/assistant_bridge.spl`
- or `src/app/mcp/assistant/dashboard_bridge.spl`

Responsibilities:

- subscribe/poll for assistant deltas
- mark freshness/staleness
- route operator actions back to MCP

## Persistent State Strategy

Use append-oriented durable records for:

- sessions
- events
- child tasks
- digest checkpoints
- notifications

Use derived summary caches for:

- active session overview
- task-tree projection
- latest digest pointers
- dashboard overview totals

Do not require full timeline replay for common read paths.

## Control APIs

Initial MCP controls:

- `assistant_start`
- `assistant_pause`
- `assistant_resume`
- `assistant_brief`
- `assistant_list_sessions`
- `assistant_get_session`
- `assistant_get_timeline`
- `assistant_push_signal`
- `assistant_list_tasks`
- `assistant_get_notifications`

Broad-scope follow-on controls:

- `assistant_subscribe`
- `assistant_ack_notification`
- `assistant_set_policy`
- `assistant_spawn_task`

## Scheduling Design

### Tick decision pipeline

1. load active session summary
2. inspect due schedules
3. merge pending external signals
4. coalesce duplicate wake reasons where allowed
5. decide `act`, `defer`, or `quiet`
6. record the decision in the timeline
7. optionally enqueue child work

### Backpressure rules

- collapse repeated identical low-priority signals into a counter/single event
- preserve urgent or operator-originated signals individually
- cap concurrent child tasks per parent session

## Child-Agent Design

### States

- `queued`
- `running`
- `waiting`
- `completed`
- `failed`
- `cancelled`
- `suppressed`

### Merge-back rules

Each child task returns:

- terminal status
- result summary
- follow-up recommendations
- retained artifacts/references

The parent session digest consumes the summary, not raw child logs.

### Ownership rules

- child tasks are append-only from the parent’s perspective except for status transitions
- parent sessions cannot mutate child history retroactively
- dashboard displays parent/child linkage directly from records

## Replay and Import Design

Standalone dashboard mode must support:

- loading persisted assistant records from local stores
- importing snapshot exports
- rebuilding session/timeline/task views without a live core

Unavailable in replay-only mode:

- pause/resume actions
- live signal push
- live child-task controls

## UI Design

### TUI / dashboard view model

Primary panels:

- session list
- selected session summary
- recent event timeline
- child-task tree
- blockers/notifications pane
- digest/brief pane

Key view states:

- live/attached
- replay/import
- degraded/stale bridge
- paused
- overloaded/backpressure active

## Error Handling

Use explicit result values and status transitions for:

- invalid session IDs
- stale bridge actions
- rejected signal payloads
- child-task spawn refusal due to policy or budget
- digest generation failure
- notification delivery failure

All such failures must leave timeline evidence.

## Verification Design

### Required coverage groups

1. session lifecycle
2. tick and signal wakeups
3. child-task spawn and merge-back
4. brief/digest generation
5. standalone dashboard replay/import
6. combined live bridge
7. degraded/failure modes

### Critical edge cases

- duplicate rapid low-priority signals
- parent session paused while child task is running
- bridge disconnect mid-update
- notification route failure
- session crash followed by restart and resumed visibility

## Implementation Order

1. session/event/task/digest records
2. session lifecycle controls
3. tick + signal pipeline
4. child-task state machine
5. dashboard collectors and core views
6. live bridge
7. notifications and broad-scope policies
8. multi-session performance hardening
