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
- `src/app/llm_dashboard/collectors/diagnostics_jsonl_collector.spl`
- `src/app/llm_dashboard/collectors/vllm_control_panel.spl`
- `src/app/web_dashboard/dashboard_html.spl`
- `src/app/web_dashboard/server.spl`

Responsibilities:

- collect snapshot/live assistant state
- build overview aggregates
- render session/timeline/task views
- support replay/import mode
- host the web login entrypoint and persist operator auth session state under `.build/llm_dashboard/auth`
- summarize diagnostics hook JSONL into an operator-visible Diagnostics panel
- render vLLM `preflight`, `start`, `poll`, `probe`, and `stop` control
  intents without importing live HTTP/process backends into normal dashboard
  rendering
- keep missing diagnostics fields rendered as explicit `none` text in
  rendered text/HTML

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

For the web login slice:

- bootstrap admin credentials come from `SIMPLE_LLM_DASHBOARD_ADMIN_USER` and `SIMPLE_LLM_DASHBOARD_ADMIN_PASSWORD`
- authenticated browser session state is stored under `.build/llm_dashboard/auth`
- clearing `.build/llm_dashboard/auth` is a destructive operator action because it invalidates active sessions

## Control APIs

Initial MCP controls:

- `assistant_start`
- `assistant_spawn_task`
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

Web-login operator failures should surface concrete guidance for:

- missing bootstrap admin environment variables
- invalid bootstrap credentials
- unwritable `.build/llm_dashboard/auth` session storage

## Verification Design

### Required coverage groups

1. session lifecycle
2. tick and signal wakeups
3. child-task spawn and merge-back
4. brief/digest generation
5. standalone dashboard replay/import
6. combined live bridge
7. degraded/failure modes
8. diagnostics JSONL collector summary and absence-safe dashboard readback

Implemented diagnostics readback coverage:

- `test/unit/app/llm_dashboard/collectors/diagnostics_jsonl_collector_spec.spl`
- `test/01_unit/app/llm_dashboard/collectors/diagnostics_jsonl_collector_spec.spl`
- `test/03_system/feature/app/web_dashboard/web_dashboard_diagnostics_panel_spec.spl`

Implemented dashboard replay/live projection coverage:

- `test/01_unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl`
- `test/unit/app/llm_dashboard/agent_dashboard_hardening_spec.spl`
- `test/01_unit/app/llm_dashboard/assistant_collectors_spec.spl`
- `test/unit/app/llm_dashboard/assistant_collectors_spec.spl`
- `test/01_unit/app/llm_dashboard/assistant_bridge_spec.spl`
- `test/unit/app/llm_dashboard/assistant_bridge_spec.spl`
- `test/01_unit/app/llm_dashboard/assistant_live_view_spec.spl`
- `test/unit/app/llm_dashboard/assistant_live_view_spec.spl`
- `test/01_unit/app/llm_dashboard/assistant_import_spec.spl`
- `test/unit/app/llm_dashboard/assistant_import_spec.spl`
- `test/01_unit/app/llm_dashboard/assistant_digest_spec.spl`
- `test/unit/app/llm_dashboard/assistant_digest_spec.spl`
- `test/01_unit/app/llm_dashboard/assistant_retention_spec.spl`
- `test/unit/app/llm_dashboard/assistant_retention_spec.spl`
- `test/01_unit/app/llm_dashboard/jsonl_watcher_spec.spl`
- `test/unit/app/llm_dashboard/jsonl_watcher_spec.spl`

The dashboard collector reads the MCP assistant file store as replay data and
selects the latest local session by `updated_at_ms`, using the session ID as a
deterministic tie-breaker. It loads sessions through the assistant store API so
timeline-merged metadata is visible in dashboard snapshots. The bridge
projection treats replay-only snapshots as read-only, fresh live snapshots as
routable to `assistant_core`, and stale or degraded snapshots as blocked with
refresh guidance. The dashboard live view converts those projections into
renderable absence-safe state lines and operator notices: fresh live sessions route
actions to `assistant_core`, while replay/stale/degraded sessions render
read-only guidance. Snapshot import writes exported sessions, timeline events,
and notifications into a selected durable replay root, then reuses the same
collector path as local file-store replay. Malformed imports return structured
errors without creating new replay records. Required snapshot arrays
(`sessions`, `timeline`, and `notifications`) are validated before any replay
streams are written, so missing arrays cannot create orphan timeline or
notification files.
Snapshot import preserves task-tree replay fields (`children`, `tool_use_ids`,
`warnings`, and `child_tasks`) and replaces per-session imported
timeline/notification streams on repeat import so replay roots do not accumulate
duplicate events from the same snapshot.
The live view also renders explicit failure evidence fields (`failure_state`,
`failure_detail`, and `failure_count`) for assistant crash metadata, missing
selected sessions, and stale/degraded bridge states. These failure lines are
absence-safe and are covered by the assistant live-view specs.
The dashboard retention projection applies bounded visible timeline and
notification windows over a snapshot, coalesces repeated low-value signal and
notification bursts, and reports retained/dropped/coalesced counts with a
absence-safe operator notice. The MCP assistant store also exposes
`assistant_store_prune_session_retention(...)`, which applies the durable side
of the same policy by rewriting persisted timeline and notification JSONL files
to bounded tails. The result reports retained/dropped counts and preserves the
current digest checkpoint id. The MCP assistant store also exposes
`assistant_store_generate_session_digest(...)`, which writes compact digest
checkpoints to a per-session digest JSONL stream, updates the session's current
digest checkpoint id, and prunes older digest checkpoints to a bounded tail.
The dashboard digest projection renders persisted summary/checkpoint readback
from replay snapshots: session summary, digest checkpoint ID, latest event
detail, task result-summary counts, warning counts, and notifications. It is
absence-safe and uses `none`/`missing` for absent data. Durable digest
generation remains owned by the MCP store path so dashboard replay can read the
same current checkpoint without becoming the source of truth.
The transcript JSONL watcher scans project directories under a dashboard root,
starts newly discovered transcript files at EOF, tails appended JSONL lines,
holds incomplete trailing records until they are newline-terminated, resets
offsets after truncation/rotation, and ignores stray files in the root.
Watcher specs use narrow `std.io_runtime` fixture helpers to avoid unrelated
runtime/process surfaces in dashboard verification.

Implemented MCP assistant control/readback coverage:

- `test/01_unit/app/mcp_unit/assistant_surface_spec.spl`
- `test/unit/app/mcp_unit/assistant_surface_spec.spl`
- `test/01_unit/app/mcp_unit/assistant_task_linking_spec.spl`
- `test/unit/app/mcp_unit/assistant_task_linking_spec.spl`
- `test/01_unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl`
- `test/unit/app/mcp_unit/assistant_dashboard_e2e_spec.spl`

The MCP control surface exposes start/spawn/pause/resume/brief/list/timeline/
signal/task/notification tools as in-process handlers. Handler readback uses
explicit optional-session matching for assistant store results, and dashboard
replay collectors expose timeline readback directly.
Signal push checks timeline persistence before returning success, and task list
rendering no longer checks impossible absent child-task records.
The dashboard collector and e2e specs use `std.io_runtime` fixture file helpers
instead of broad `app.io.mod` imports, so they pass without internal
process-exit diagnostics.

Implemented assistant store/view hardening:

- root-facing assistant store APIs normalize parsed JSON tool input
- root-facing `any` APIs reject non-object parsed values
- typed session creation generates missing session IDs for valid session objects
- typed MCP assistant callers use record-specific store functions
- session detail recomputes event counts from timeline records rather than
  accumulating stale stored counts across loads
- state updates increment persisted event metadata before writing session JSON
- compact briefs render numeric counts with `str(...)`, not placeholder text
- incoming parsed JSON signal events normalize persisted event kind to
  `signal_event`, preserving the operator-visible wake reason in `signal`

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
