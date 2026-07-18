# Tmp View Min Specification

> <details>

<!-- sdn-diagram:id=tmp_view_min_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_view_min_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_view_min_spec -> std
tmp_view_min_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_view_min_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp View Min Specification

## Scenarios

### min view

#### creates and details

- file write
- file write
   - Expected: created == nil is false
- file write
- assistant store append event
- file write
- file write
   - Expected: detail == nil is false
- file write


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/simple-min-view-{rt_time_now_unix_micros()}"
val marker = "/tmp/simple-min-view-marker"
file_write(marker, "start")
val session_id = "min-view"
val created = assistant_store_create_session(root, json_parse(r"""{"session_id":"min-view","name":"Min","summary":"min","objective":"min","prompt":"min","mode":"proactive","state":"running"}"""))
file_write(marker, "created")
expect(created == nil).to_equal(false)
file_write(marker, "expect-created")
assistant_store_append_event(root, json_parse(r"""{"session_id":"min-view","kind":"note","message":"first","timestamp_ms":1000}"""))
file_write(marker, "appended")
val detail = assistant_store_session_detail(root, session_id)
file_write(marker, "detail")
expect(detail == nil).to_equal(false)
file_write(marker, "done")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_view_min_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- min view

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
