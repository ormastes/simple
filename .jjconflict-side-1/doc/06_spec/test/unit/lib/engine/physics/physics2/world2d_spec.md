# World2d Specification

> <details>

<!-- sdn-diagram:id=world2d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=world2d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

world2d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=world2d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# World2d Specification

## Scenarios

### PhysicsWorld2D

#### creates with default config

- var world = PhysicsWorld2D create
   - Expected: world.body_count() equals `0`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
expect(world.body_count()).to_equal(0)
world.destroy()
```

</details>

#### adds dynamic body

- var world = PhysicsWorld2D create
   - Expected: world.body_count() equals `1`
   - Expected: idx equals `0`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
val idx = world.add_dynamic_body(node, 0.0, 5.0, 1.0)
expect(world.body_count()).to_equal(1)
expect(idx).to_equal(0)
world.destroy()
```

</details>

#### adds static body

- var world = PhysicsWorld2D create
   - Expected: world.body_count() equals `1`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(2)
val idx = world.add_static_body(node, 0.0, 0.0)
expect(world.body_count()).to_equal(1)
world.destroy()
```

</details>

#### body falls under gravity

- var config = default physics config 2d
- var world = PhysicsWorld2D create
- world add dynamic body
- world add circle collider
- world step
   - Expected: pos.y < 10.0 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.backend = PhysicsBackend.CpuScalar
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_dynamic_body(node, 0.0, 10.0, 1.0)
world.add_circle_collider(node, 0.5)
world.step(0.1)
val pos = world.get_position(node)
expect(pos.y < 10.0).to_equal(true)
world.destroy()
```

</details>

#### static body does not move

- var config = default physics config 2d
- var world = PhysicsWorld2D create
- world add static body
- world step
   - Expected: pos.x equals `5.0`
   - Expected: pos.y equals `3.0`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.backend = PhysicsBackend.CpuScalar
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_static_body(node, 5.0, 3.0)
world.step(0.1)
val pos = world.get_position(node)
expect(pos.x).to_equal(5.0)
expect(pos.y).to_equal(3.0)
world.destroy()
```

</details>

#### collision stops falling body on floor

- var config = default physics config 2d
- var world = PhysicsWorld2D create
- world add static body
- world add box collider
- world add dynamic body
- world add circle collider
- world step
   - Expected: pos.y > -1.0 is true
   - Expected: pos.y < 3.0 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.backend = PhysicsBackend.CpuScalar
var world = PhysicsWorld2D.create(config)
val floor_id = make_node(1)
val ball_id = make_node(2)
world.add_static_body(floor_id, 0.0, 0.0)
world.add_box_collider(floor_id, 10.0, 0.5)
world.add_dynamic_body(ball_id, 0.0, 2.0, 1.0)
world.add_circle_collider(ball_id, 0.5)
var step = 0
while step < 200:
    world.step(0.016)
    step = step + 1
val pos = world.get_position(ball_id)
expect(pos.y > -1.0).to_equal(true)
expect(pos.y < 3.0).to_equal(true)
world.destroy()
```

</details>

#### apply_force accelerates body

- var config = default physics config 2d
- var world = PhysicsWorld2D create
- world add dynamic body
- world add circle collider
- world apply force
- world step
   - Expected: vel.x > 0.0 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.backend = PhysicsBackend.CpuScalar
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_dynamic_body(node, 0.0, 0.0, 1.0)
world.add_circle_collider(node, 0.5)
world.apply_force(node, 10.0, 0.0)
world.step(0.1)
val vel = world.get_velocity(node)
expect(vel.x > 0.0).to_equal(true)
world.destroy()
```

</details>

#### get_all_dynamic_transforms returns only dynamic bodies

- var config = default physics config 2d
- var world = PhysicsWorld2D create
- world add static body
- world add dynamic body
- world add dynamic body
   - Expected: transforms.len() equals `2`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.backend = PhysicsBackend.CpuScalar
var world = PhysicsWorld2D.create(config)
val s = make_node(1)
val d1 = make_node(2)
val d2 = make_node(3)
world.add_static_body(s, 0.0, 0.0)
world.add_dynamic_body(d1, 1.0, 1.0, 1.0)
world.add_dynamic_body(d2, 2.0, 2.0, 1.0)
val transforms = world.get_all_dynamic_transforms()
expect(transforms.len()).to_equal(2)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/engine/physics/physics2/world2d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PhysicsWorld2D

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
