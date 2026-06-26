# Assistant Import Specification

> <details>

<!-- sdn-diagram:id=assistant_import_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_import_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_import_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_import_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Import Specification

## Scenarios

### assistant dashboard snapshot import

#### imports a durable snapshot into a replay root and collector reads it

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = import_root("roundtrip")
val session_id = "imported-session"
val result = assistant_dashboard_import_snapshot(root, import_payload(session_id))

expect(result.imported).to_equal(true)
expect(result.session_count).to_equal(1)
expect(result.timeline_count).to_equal(1)
expect(result.notification_count).to_equal(1)
expect(result.error).to_equal("")

val snapshot = collect_assistant_snapshot_from_root(root)
expect(snapshot.selected_session_id).to_equal(session_id)
expect(snapshot.total_sessions).to_equal(1)
expect(snapshot.timeline.len()).to_equal(1)
expect(snapshot.notifications.len()).to_equal(1)
expect(snapshot.sessions[0].objective).to_equal("Imported Objective")
```

</details>

#### preserves child task metadata and replaces snapshot streams on repeat import

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = import_root("tasks")
val session_id = "imported-task-session"
val first = assistant_dashboard_import_snapshot(root, import_payload_with_child_task(session_id))
val second = assistant_dashboard_import_snapshot(root, import_payload_with_child_task(session_id))

expect(first.imported).to_equal(true)
expect(second.imported).to_equal(true)

val snapshot = collect_assistant_snapshot_from_root(root)
expect(snapshot.timeline.len()).to_equal(1)
expect(snapshot.notifications.len()).to_equal(1)
expect(snapshot.sessions[0].children.len()).to_equal(1)
expect(snapshot.sessions[0].tool_use_ids.len()).to_equal(1)
expect(snapshot.sessions[0].warnings.len()).to_equal(1)
expect(snapshot.sessions[0].child_tasks.len()).to_equal(1)
expect(snapshot.sessions[0].child_tasks[0].task_id).to_equal("task-1")
expect(snapshot.sessions[0].child_tasks[0].child_session_id).to_equal("child-session")
```

</details>

#### rejects malformed import payloads without creating a replay snapshot

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = import_root("invalid")
val result = assistant_dashboard_import_snapshot(root, "{\"sessions\":{}}")

expect(result.imported).to_equal(false)
expect(result.session_count).to_equal(0)
expect(result.error).to_equal("sessions must be an array")

val snapshot = collect_assistant_snapshot_from_root(root)
expect(snapshot.total_sessions).to_equal(0)
```

</details>

#### rejects missing required snapshot arrays before writing streams

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = import_root("missing-arrays")
val result = assistant_dashboard_import_snapshot(root, "{\"timeline\":[{\"event_id\":\"event-1\",\"session_id\":\"orphan\",\"kind\":\"note\"}],\"notifications\":[]}")

expect(result.imported).to_equal(false)
expect(result.timeline_count).to_equal(0)
expect(result.error).to_equal("sessions must be an array")

val snapshot = collect_assistant_snapshot_from_root(root)
expect(snapshot.total_sessions).to_equal(0)
expect(snapshot.timeline.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/assistant_import_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant dashboard snapshot import

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
