# Physics Xpbd Specification

> 1. var world = make rope

<!-- sdn-diagram:id=physics_xpbd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_xpbd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_xpbd_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_xpbd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Xpbd Specification

## Scenarios

### Physics2 XPBD Rope System

#### rope sags under gravity

1. var world = make rope
2. step rope
   - Expected: bottom < -0.3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_rope(8, 0.5, 50.0)
step_rope(world, 60)
val bottom = get_bottom_y(world, 8)
expect(bottom < -0.3).to_equal(true)
```

</details>

#### fixed particle stays at origin

1. var world = make rope
2. step rope
   - Expected: pos.0 equals `0.0`
   - Expected: pos.1 equals `0.0`
   - Expected: pos.2 equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_rope(5, 0.5, 100.0)
step_rope(world, 40)
val pos = world.get_position(0)
expect(pos.0).to_equal(0.0)
expect(pos.1).to_equal(0.0)
expect(pos.2).to_equal(0.0)
```

</details>

#### particles stay bounded

1. var world = make rope
2. step rope
   - Expected: all_bounded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_rope(6, 0.5, 50.0)
step_rope(world, 80)
var i = 0
var all_bounded = true
while i < 6:
    val pos = world.get_position(i)
    if pos.0 < -20.0 or pos.0 > 20.0:
        all_bounded = false
    if pos.1 < -20.0 or pos.1 > 20.0:
        all_bounded = false
    i = i + 1
expect(all_bounded).to_equal(true)
```

</details>

#### end particle below start

1. var world = make rope
2. step rope
   - Expected: end_pos.1 < 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_rope(5, 0.5, 80.0)
step_rope(world, 50)
val end_pos = world.get_position(4)
expect(end_pos.1 < 0.0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_xpbd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 XPBD Rope System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
