# Access Query Json Specification

> <details>

<!-- sdn-diagram:id=access_query_json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=access_query_json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

access_query_json_spec -> std
access_query_json_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=access_query_json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Access Query Json Specification

## Scenarios

### UI access JSON array serialization

#### keeps surfaces nodes child ids actions and events in stable order

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = ui_access_snapshot_to_json(_json_snapshot())

expect(json).to_equal("{\"protocol_version\":1,\"snapshot_revision\":9,\"mode\":\"normal\",\"active_surface\":\"main\",\"surfaces\":[{\"surface_id\":\"main\",\"title\":\"Main\",\"active\":true,\"window_id\":\"w1\",\"app_id\":\"app.main\",\"root_canonical_id\":\"main#root\"},{\"surface_id\":\"popup\",\"title\":\"Popup\",\"active\":false,\"window_id\":\"w2\",\"app_id\":\"app.popup\",\"root_canonical_id\":\"popup#root\"}],\"nodes\":[{\"canonical_id\":\"main#root\",\"surface_id\":\"main\",\"widget_id\":\"root\",\"kind\":\"panel\",\"visible\":true,\"focused\":false,\"enabled\":true,\"selected\":false,\"text\":\"\",\"props\":{},\"child_ids\":[\"main#save\",\"main#cancel\"],\"action_names\":[]},{\"canonical_id\":\"main#save\",\"surface_id\":\"main\",\"widget_id\":\"save\",\"kind\":\"button\",\"visible\":true,\"focused\":true,\"enabled\":true,\"selected\":false,\"text\":\"Save\",\"props\":{},\"child_ids\":[],\"action_names\":[\"save\",\"submit\"]}],\"recent_events\":[{\"surface_id\":\"main\",\"widget_id\":\"save\",\"canonical_id\":\"main#save\",\"event_kind\":\"action\",\"payload\":\"save\",\"sequence\":9}]}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/access_query_json_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- UI access JSON array serialization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
