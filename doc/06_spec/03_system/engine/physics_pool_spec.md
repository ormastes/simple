# Physics Pool Specification

> 1. var world = make pool world

<!-- sdn-diagram:id=physics_pool_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_pool_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_pool_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_pool_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Pool Specification

## Scenarios

### Physics2 Pool System

#### cue ball moves after impulse

1. var world = make pool world
2. world apply impulse
3. step n
   - Expected: pos.x > -2.0 is true
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_pool_world()
world.apply_impulse(make_node(0), 5.0, 0.0)
step_n(world, 30)
val pos = world.get_position(make_node(0))
expect(pos.x > -2.0).to_equal(true)
world.destroy()
```

</details>

#### positions remain finite after simulation

1. var world = make pool world
2. world apply impulse
3. step n
   - Expected: check_positions_finite(world) is true
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_pool_world()
world.apply_impulse(make_node(0), 5.0, 0.3)
step_n(world, 100)
expect(check_positions_finite(world)).to_equal(true)
world.destroy()
```

</details>

#### kinetic energy bounded

1. var world = make pool world
2. world apply impulse
3. step n
   - Expected: ke < 50.0 is true
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_pool_world()
world.apply_impulse(make_node(0), 5.0, 0.0)
step_n(world, 100)
val ke = get_total_ke(world)
expect(ke < 50.0).to_equal(true)
world.destroy()
```

</details>

#### deterministic across two runs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r1 = run_deterministic(5.0, 0.1, 80)
val r2 = run_deterministic(5.0, 0.1, 80)
expect(r1.0).to_equal(r2.0)
expect(r1.1).to_equal(r2.1)
```

</details>

#### target ball gets displaced by collision

1. var config = default physics config 2d
2. config gravity = Vec2
3. var world = PhysicsWorld2D create
4. world add dynamic body
5. world add circle collider
6. world add dynamic body
7. world add circle collider
8. world apply impulse
9. step n
   - Expected: after.x > 1.0 is true
10. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
config.restitution = 0.9
config.backend = PhysicsBackend.CpuScalar
var world = PhysicsWorld2D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 0.0, 1.0)
world.add_circle_collider(make_node(0), 0.5)
world.add_dynamic_body(make_node(1), 0.8, 0.0, 1.0)
world.add_circle_collider(make_node(1), 0.5)
world.apply_impulse(make_node(0), 5.0, 0.0)
step_n(world, 10)
val after = world.get_position(make_node(1))
expect(after.x > 1.0).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_pool_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 Pool System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
