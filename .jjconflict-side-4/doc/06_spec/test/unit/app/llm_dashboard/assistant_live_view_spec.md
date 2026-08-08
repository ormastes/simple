# Assistant Live View Specification

> <details>

<!-- sdn-diagram:id=assistant_live_view_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_live_view_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_live_view_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_live_view_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Live View Specification

## Scenarios

### assistant dashboard live view

#### renders replay snapshots as read-only without internal absence marker text

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_session("session-replay", 1000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 2_000_000, 1_000_000, false)
val lines = assistant_dashboard_render_live_view(view)
val rendered = lines.join("\n")

expect(view.read_only).to_equal(true)
expect(view.live_controls_enabled).to_equal(false)
expect(view.primary_action.route_target).to_equal("blocked")
expect_absence_marker_hidden(rendered)
expect(rendered).to_contain("replay snapshot is read-only")
```

</details>

#### routes fresh live snapshots to assistant_core and exposes task counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_session("session-live", 2000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 2_000_100, 2_000_000, true)

expect(view.read_only).to_equal(false)
expect(view.live_controls_enabled).to_equal(true)
expect(view.freshness_state).to_equal("fresh")
expect(view.task_count).to_equal(1)
expect(view.primary_action.allowed).to_equal(true)
expect(view.primary_action.route_target).to_equal("assistant_core")
```

</details>

#### blocks stale live snapshots and asks the operator to refresh

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_session("session-stale", 3000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 50_000_000, 1_000_000, true)
val lines = assistant_dashboard_render_live_view(view)

expect(view.read_only).to_equal(true)
expect(view.live_controls_enabled).to_equal(false)
expect(view.freshness_state).to_equal("stale")
expect(view.primary_action.allowed).to_equal(false)
expect(view.failure_state).to_equal("bridge_stale")
expect(lines.join("\n")).to_contain("refresh required before operator actions")
```

</details>

#### renders assistant crash evidence from failed session metadata

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val snapshot = make_snapshot(make_failed_session("session-crash", 4000))
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 4_000_100, 4_000_000, true)
val lines = assistant_dashboard_render_live_view(view)
val rendered = lines.join("\n")

expect(view.failure_state).to_equal("error")
expect(view.failure_count).to_equal(1)
expect(view.failure_detail).to_equal("model process crashed")
expect(rendered).to_contain("failure error model process crashed")
expect_absence_marker_hidden(rendered)
```

</details>

#### renders missing selected-session evidence without internal absence marker text

- expect absence marker hidden


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val policy = assistant_bridge_default_policy()
val snapshot = AssistantDashboardSnapshot(
    selected_session_id: "missing-session",
    total_sessions: 0,
    sessions: [],
    timeline: [],
    notifications: [],
    source_root: ".build/llm_dashboard/assistant",
    mode: "replay"
)
val view = assistant_dashboard_live_view_from_snapshot(snapshot, policy, 1_000_000, 1_000_000, false)
val lines = assistant_dashboard_render_live_view(view)
val rendered = lines.join("\n")

expect(view.failure_state).to_equal("missing")
expect(view.failure_detail).to_equal("selected session unavailable")
expect_absence_marker_hidden(rendered)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/assistant_live_view_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant dashboard live view

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
