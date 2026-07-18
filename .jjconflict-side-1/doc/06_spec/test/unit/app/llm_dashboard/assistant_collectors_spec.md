# Assistant Collectors Specification

> <details>

<!-- sdn-diagram:id=assistant_collectors_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=assistant_collectors_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

assistant_collectors_spec -> app
assistant_collectors_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=assistant_collectors_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Assistant Collectors Specification

## Scenarios

### assistant dashboard collectors

#### replays a local assistant store session and timeline

- dir create all
- dir create all
- file write
- file write
   - Expected: snapshot.selected_session_id equals `session_id`
- file delete
- file delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session_id = assistant_fixture_session_id()
val session_path = assistant_fixture_session_path(session_id)
val timeline_path = assistant_fixture_timeline_path(session_id)

dir_create_all("{assistant_fixture_root()}/sessions")
dir_create_all("{assistant_fixture_root()}/timelines")
file_write(session_path, assistant_fixture_session_json(session_id))
file_write(timeline_path, assistant_fixture_timeline_jsonl())

val snapshot = collect_assistant_snapshot_from_root(assistant_fixture_root())

expect(snapshot.selected_session_id).to_equal(session_id)
expect(snapshot.total_sessions).to_be_greater_than(0)
expect(snapshot.timeline.len()).to_be_greater_than(0)

file_delete(session_path)
file_delete(timeline_path)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/llm_dashboard/assistant_collectors_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- assistant dashboard collectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
