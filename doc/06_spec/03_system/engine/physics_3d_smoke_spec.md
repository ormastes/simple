# Physics 3d Smoke Specification

> 1. var config = default physics config 3d

<!-- sdn-diagram:id=physics_3d_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_3d_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_3d_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_3d_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics 3d Smoke Specification

## Scenarios

### Physics2 3D Smoke Test

#### sphere falls under gravity

1. var config = default physics config 3d
2. var world = PhysicsWorld3D create
3. world add dynamic body
4. world add sphere collider
5. step 3d
   - Expected: pos.y < 10.0 is true
   - Expected: pos.y > -50.0 is true
6. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 10.0, 0.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
step_3d(world, 30)
val pos = world.get_position(make_node(0))
expect(pos.y < 10.0).to_equal(true)
expect(pos.y > -50.0).to_equal(true)
world.destroy()
```

</details>

#### x and z unchanged for vertical drop

1. var config = default physics config 3d
2. var world = PhysicsWorld3D create
3. world add dynamic body
4. world add sphere collider
5. step 3d
   - Expected: math_abs(pos.x - 3.0) < 0.01 is true
   - Expected: math_abs(pos.z - (-2.0)) < 0.01 is true
6. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 3.0, 10.0, -2.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
step_3d(world, 20)
val pos = world.get_position(make_node(0))
expect(math_abs(pos.x - 3.0) < 0.01).to_equal(true)
expect(math_abs(pos.z - (-2.0)) < 0.01).to_equal(true)
world.destroy()
```

</details>

#### body count correct

1. var config = default physics config 3d
2. var world = PhysicsWorld3D create
3. world add dynamic body
4. world add sphere collider
5. world add static body
6. world add box collider
   - Expected: world.body_count() == 2 is true
7. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 5.0, 0.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
world.add_static_body(make_node(1), 0.0, 0.0, 0.0)
world.add_box_collider(make_node(1), 5.0, 0.5, 5.0)
expect(world.body_count() == 2).to_equal(true)
world.destroy()
```

</details>

#### velocity increases during fall

1. var config = default physics config 3d
2. var world = PhysicsWorld3D create
3. world add dynamic body
4. world add sphere collider
5. step 3d
   - Expected: vel.y < -0.1 is true
6. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_dynamic_body(make_node(0), 0.0, 10.0, 0.0, 1.0)
world.add_sphere_collider(make_node(0), 0.5)
step_3d(world, 10)
val vel = world.get_velocity(make_node(0))
expect(vel.y < -0.1).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_3d_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 3D Smoke Test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
