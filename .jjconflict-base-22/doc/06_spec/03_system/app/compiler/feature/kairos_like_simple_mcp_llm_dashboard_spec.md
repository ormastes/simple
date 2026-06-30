# Kairos Like Simple Mcp Llm Dashboard Specification

> <details>

<!-- sdn-diagram:id=kairos_like_simple_mcp_llm_dashboard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kairos_like_simple_mcp_llm_dashboard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kairos_like_simple_mcp_llm_dashboard_spec -> std
kairos_like_simple_mcp_llm_dashboard_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kairos_like_simple_mcp_llm_dashboard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kairos Like Simple Mcp Llm Dashboard Specification

## Scenarios

### KAIROS-like simple mcp and llm dashboard

### REQ-KAIROS-001: session identity and lifecycle

#### should create and persist an assistant session with stable identity

- create session
   - Expected: session.session_id equals `assistant-kairos-identity`
   - Expected: session.objective equals `coordinate agents`
- fail
   - Expected: assistant_store_list_sessions(root).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("identity")
create_session(root, "assistant-kairos-identity")

val loaded = assistant_store_load_session(root, "assistant-kairos-identity")
match loaded:
    case Some(session):
        expect(session.session_id).to_equal("assistant-kairos-identity")
        expect(session.objective).to_equal("coordinate agents")
    case nil:
        fail("persisted assistant session should load")
expect(assistant_store_list_sessions(root).len()).to_equal(1)
```

</details>

#### should allow a paused session to resume with preserved state

- create session
- assistant store update state
   - Expected: session.state equals `running`
   - Expected: session.last_signal equals `resume`
   - Expected: session.event_count equals `2`
- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("resume")
create_session(root, "assistant-kairos-resume")
assistant_store_update_state(root, "assistant-kairos-resume", "paused", "pause")
val resumed = assistant_store_update_state(root, "assistant-kairos-resume", "running", "resume")

match resumed:
    case Some(session):
        expect(session.state).to_equal("running")
        expect(session.last_signal).to_equal("resume")
        expect(session.event_count).to_equal(2)
    case nil:
        fail("assistant session should resume")
```

</details>

### REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals

#### should record a periodic tick wake reason in the session timeline

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("tick", "assistant-kairos-tick")
val timeline = assistant_store_collect_timeline(root, "assistant-kairos-tick", 10, 0)

expect(timeline[0].kind).to_equal("tick")
expect(timeline[0].signal).to_equal("tick")
expect(timeline[0].message).to_equal("periodic wake")
```

</details>

#### should record an external signal wakeup with source metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("signal", "assistant-kairos-signal")
val timeline = assistant_store_collect_timeline(root, "assistant-kairos-signal", 10, 0)

expect(timeline[1].kind).to_equal("signal_event")
expect(timeline[1].signal).to_equal("operator")
expect(timeline[1].source).to_equal("assistant")
```

</details>

### REQ-KAIROS-004: child-agent delegation

#### should track a child task with parent linkage and terminal summary

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("child", "assistant-kairos-child")
val loaded = assistant_store_load_session(root, "assistant-kairos-child")

match loaded:
    case Some(session):
        expect(session.children[0]).to_equal("assistant-child-1")
        expect(session.child_tasks[0].session_id).to_equal("assistant-kairos-child")
        expect(session.child_tasks[0].status).to_equal("completed")
        expect(session.child_tasks[0].result_summary).to_equal("child completed")
    case nil:
        fail("assistant session should include child task")
```

</details>

### REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications

#### should produce a compact brief from recent session activity

- expect internal absence hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("brief", "assistant-kairos-brief")
val brief = assistant_store_session_brief(root, "assistant-kairos-brief")

expect(brief).to_contain("session: assistant-kairos-brief")
expect(brief).to_contain("summary: coordinate agents")
expect(brief).to_contain("timeline events: 3")
expect_internal_absence_hidden(brief)
```

</details>

#### should preserve notification decision and delivery status

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("notify", "assistant-kairos-notify")
val notifications = assistant_store_collect_notifications(root, "assistant-kairos-notify", 10, 0)

expect(notifications.len()).to_equal(3)
expect(notifications[2].kind).to_equal("child_task")
expect(notifications[2].signal).to_equal("completed")
```

</details>

### REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes

#### should support standalone simple mcp control without the dashboard

- fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("standalone-mcp", "assistant-kairos-mcp")
val loaded = assistant_store_load_session(root, "assistant-kairos-mcp")

match loaded:
    case Some(session):
        expect(session.mode).to_equal("proactive")
        expect(session.policy).to_equal("bounded")
        expect(session.event_count).to_equal(3)
    case nil:
        fail("assistant mcp store should work without dashboard routes")
```

</details>

#### should support standalone dashboard replay without live mcp

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("standalone-dashboard", "assistant-kairos-replay")
val snapshot = selected_snapshot(root, "assistant-kairos-replay")
val view = assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 2_000_000, 1_000_000, false)

expect(snapshot.mode).to_equal("replay")
expect(view.read_only).to_equal(true)
expect(view.primary_action.route_target).to_equal("blocked")
```

</details>

### REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode

#### should attach dashboard live state without moving source of truth

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("live", "assistant-kairos-live")
val snapshot = selected_snapshot(root, "assistant-kairos-live")
val view = assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 2_000_100, 2_000_000, true)

expect(view.mode).to_equal("live")
expect(view.live_controls_enabled).to_equal(true)
expect(view.primary_action.route_target).to_equal("assistant_core")
```

</details>

#### should expose operator-visible task tree and recent events

- expect internal absence hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = populated_root("visible", "assistant-kairos-visible")
val snapshot = selected_snapshot(root, "assistant-kairos-visible")
val live_lines = assistant_dashboard_render_live_view(assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 2_000_100, 2_000_000, true))
val digest_lines = assistant_dashboard_render_digest(assistant_dashboard_digest_from_snapshot(snapshot))

expect(live_lines.join("\n")).to_contain("timeline 3 tasks 1 notifications 3")
expect(digest_lines.join("\n")).to_contain("task_summaries 1")
expect_internal_absence_hidden((live_lines + digest_lines).join("\n"))
```

</details>

### REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention

#### should preserve structured failure evidence after a child-task crash

- create session
- append event
   - Expected: view.failure_state equals `error`
   - Expected: view.failure_detail equals `child crashed`
   - Expected: view.failure_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("failure")
create_session(root, "assistant-kairos-failure")
append_event(root, "assistant-kairos-failure", "error", "child crashed", "failed", 1000)
val snapshot = selected_snapshot(root, "assistant-kairos-failure")
val view = assistant_dashboard_live_view_from_snapshot(snapshot, assistant_bridge_default_policy(), 1_000_100, 1_000_000, true)

expect(view.failure_state).to_equal("error")
expect(view.failure_detail).to_equal("child crashed")
expect(view.failure_count).to_equal(1)
```

</details>

#### should apply bounded retention or coalescing under bursty signals

- create session
- append event
   - Expected: durable.status equals `pruned`
   - Expected: durable.dropped_timeline_count equals `3`
   - Expected: projection.backpressure_state equals `backpressure`
   - Expected: projection.coalesced_signal_count equals `1`
- expect internal absence hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = test_root("retention")
create_session(root, "assistant-kairos-retention")
var i: i64 = 0
while i < 7:
    append_event(root, "assistant-kairos-retention", "signal", "wake", "operator", i + 1)
    i = i + 1

val durable = assistant_store_prune_session_retention(root, "assistant-kairos-retention", 4, 3)
val snapshot = selected_snapshot(root, "assistant-kairos-retention")
val policy = AssistantDashboardRetentionPolicy(
    max_timeline_events: 3,
    max_notifications: 2,
    coalesce_after_repeats: 2,
    backpressure_after_dropped: 1
)
val projection = assistant_dashboard_retention_projection(snapshot, policy)

expect(durable.status).to_equal("pruned")
expect(durable.dropped_timeline_count).to_equal(3)
expect(projection.backpressure_state).to_equal("backpressure")
expect(projection.coalesced_signal_count).to_equal(1)
expect_internal_absence_hidden(projection.notice)
```

</details>

### absence-safe web route contract

#### should render authenticated /agents without internal absence markers

- expect internal absence hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server = DashboardServer.new_with_agent_dir(3099, ".build/llm_dashboard/agent-system-empty")
val response = server.route_http("GET", "/agents", "", "sid")

expect(response).to_contain("HTTP/1.1 200 OK")
expect(response).to_contain("selected session unavailable")
expect_internal_absence_hidden(response)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/compiler/feature/kairos_like_simple_mcp_llm_dashboard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- KAIROS-like simple mcp and llm dashboard
- REQ-KAIROS-001: session identity and lifecycle
- REQ-KAIROS-002 and REQ-KAIROS-003: ticks and signals
- REQ-KAIROS-004: child-agent delegation
- REQ-KAIROS-005 and REQ-KAIROS-006: briefs and notifications
- REQ-KAIROS-007 and REQ-KAIROS-008: standalone modes
- REQ-KAIROS-009 and REQ-KAIROS-010: combined live mode
- REQ-KAIROS-011 and REQ-KAIROS-012: recovery and bounded retention
- absence-safe web route contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
