# Physics Stacking Specification

> 1. var world = make stack world

<!-- sdn-diagram:id=physics_stacking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_stacking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_stacking_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_stacking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Stacking Specification

## Scenarios

### Physics2 Stacking System

#### crates settle above floor

1. var world = make stack world
2. step n
   - Expected: all_above_floor(world, 3) is true
3. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_stack_world(3)
step_n(world, 100)
expect(all_above_floor(world, 3)).to_equal(true)
world.destroy()
```

</details>

#### stack height bounded

1. var world = make stack world
2. step n
   - Expected: h < 10.0 is true
   - Expected: h > 0.5 is true
3. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_stack_world(3)
step_n(world, 100)
val h = max_height(world, 3)
expect(h < 10.0).to_equal(true)
expect(h > 0.5).to_equal(true)
world.destroy()
```

</details>

#### gravity pulls crates down

1. var world = make stack world
2. step n
   - Expected: after.y < before.y is true
3. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_stack_world(1)
val before = world.get_position(make_node(1))
step_n(world, 20)
val after = world.get_position(make_node(1))
expect(after.y < before.y).to_equal(true)
world.destroy()
```

</details>

#### floor stops falling crate

1. var world = make stack world
2. step n
   - Expected: pos.y > 0.0 is true
   - Expected: pos.y < 3.0 is true
3. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_stack_world(1)
step_n(world, 150)
val pos = world.get_position(make_node(1))
expect(pos.y > 0.0).to_equal(true)
expect(pos.y < 3.0).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_stacking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 Stacking System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
