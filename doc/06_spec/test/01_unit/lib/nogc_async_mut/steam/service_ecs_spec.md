# Service Ecs Specification

> <details>

<!-- sdn-diagram:id=service_ecs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=service_ecs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

service_ecs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=service_ecs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Service Ecs Specification

## Scenarios

### Steam/Proton ECS World

#### create_session returns positive entity_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("480", "Half-Life 2", "steamapps/compatdata/480/pfx")
expect(eid).to_be_greater_than(0)
```

</details>

#### create_session returns 0 on missing app_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("", "HL2", "steamapps/compatdata/480/pfx")
expect(eid).to_equal(0)
```

</details>

#### create_session returns 0 on missing prefix_path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("480", "HL2", "")
expect(eid).to_equal(0)
```

</details>

#### get_app_id returns the correct app_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("570", "Dota 2", "steamapps/compatdata/570/pfx")
expect(steam_ecs_get_app_id(eid)).to_equal("570")
```

</details>

#### get_app_id returns empty string for invalid entity

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(steam_ecs_get_app_id(0)).to_equal("")
```

</details>

#### initial phase is created

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("730", "CS:GO", "steamapps/compatdata/730/pfx")
expect(steam_ecs_get_phase(eid)).to_equal("created")
```

</details>

#### set_phase updates phase correctly

1. steam ecs set phase
   - Expected: steam_ecs_get_phase(eid) equals `container-ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
steam_ecs_set_phase(eid, "container-ready")
expect(steam_ecs_get_phase(eid)).to_equal("container-ready")
```

</details>

#### set_container does not change phase

1. steam ecs set container
   - Expected: steam_ecs_get_phase(eid) equals `created`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
steam_ecs_set_container(eid, 42)
expect(steam_ecs_get_phase(eid)).to_equal("created")
```

</details>

#### two sessions have distinct entity ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
val e2 = steam_ecs_create_session("570", "Dota 2", "steamapps/compatdata/570/pfx")
expect(e1).to_not_equal(e2)
```

</details>

#### destroy makes entity unreachable

1. steam ecs destroy
   - Expected: steam_ecs_get_app_id(eid) equals ``
   - Expected: steam_ecs_get_phase(eid) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eid = steam_ecs_create_session("480", "HL2", "steamapps/compatdata/480/pfx")
steam_ecs_destroy(eid)
expect(steam_ecs_get_app_id(eid)).to_equal("")
expect(steam_ecs_get_phase(eid)).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/steam/service_ecs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Steam/Proton ECS World

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
