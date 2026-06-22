# Physics Cloth Specification

> 1. var world = make cloth

<!-- sdn-diagram:id=physics_cloth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_cloth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_cloth_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_cloth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Cloth Specification

## Scenarios

### Physics2 XPBD Cloth System

#### cloth sags under gravity

1. var world = make cloth
2. step cloth
   - Expected: avg_y < -1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_cloth()
step_cloth(world, 80)
val avg_y = get_bottom_row_avg_y(world)
expect(avg_y < -1.0).to_equal(true)
```

</details>

#### top row stays fixed

1. var world = make cloth
2. step cloth
   - Expected: fixed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_cloth()
step_cloth(world, 60)
val fixed = check_top_row_fixed(world)
expect(fixed).to_equal(true)
```

</details>

#### all particles bounded

1. var world = make cloth
2. step cloth
   - Expected: bounded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_cloth()
step_cloth(world, 100)
val bounded = check_all_bounded(world)
expect(bounded).to_equal(true)
```

</details>

#### cloth width preserved

1. var world = make cloth
2. step cloth
   - Expected: width > 2.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_cloth()
step_cloth(world, 60)
val min_x = get_min_x(world)
val max_x = get_max_x(world)
val width = max_x - min_x
expect(width > 2.0).to_equal(true)
```

</details>

#### constraint convergence

1. var world = make cloth
2. step cloth
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_cloth()
step_cloth(world, 100)
val ok = check_constraints_reasonable(world)
expect(ok).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_cloth_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 XPBD Cloth System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
