# World3d Specification

> 1. var world = PhysicsWorld3D create

<!-- sdn-diagram:id=world3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=world3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

world3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=world3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# World3d Specification

## Scenarios

### PhysicsWorld3D

#### creates with default config

1. var world = PhysicsWorld3D create
   - Expected: world.body_count() equals `0`
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
expect(world.body_count()).to_equal(0)
world.destroy()
```

</details>

#### body falls under 3D gravity

1. var world = PhysicsWorld3D create
2. world add dynamic body
3. world add sphere collider
4. world step
   - Expected: pos.y < 10.0 is true
   - Expected: pos.x equals `0.0`
   - Expected: pos.z equals `0.0`
5. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
val node = make_node(1)
world.add_dynamic_body(node, 0.0, 10.0, 0.0, 1.0)
world.add_sphere_collider(node, 0.5)
world.step(0.1)
val pos = world.get_position(node)
expect(pos.y < 10.0).to_equal(true)
expect(pos.x).to_equal(0.0)
expect(pos.z).to_equal(0.0)
world.destroy()
```

</details>

#### static body stays put

1. var world = PhysicsWorld3D create
2. world add static body
3. world step
   - Expected: pos.x equals `3.0`
   - Expected: pos.y equals `5.0`
   - Expected: pos.z equals `7.0`
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
val node = make_node(1)
world.add_static_body(node, 3.0, 5.0, 7.0)
world.step(0.1)
val pos = world.get_position(node)
expect(pos.x).to_equal(3.0)
expect(pos.y).to_equal(5.0)
expect(pos.z).to_equal(7.0)
world.destroy()
```

</details>

#### sphere collision detected

1. var world = PhysicsWorld3D create
2. world add static body
3. world add box collider
4. world add dynamic body
5. world add sphere collider
6. world step
   - Expected: pos.y > -1.0 is true
7. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
val floor = make_node(0)
world.add_static_body(floor, 0.0, 0.0, 0.0)
world.add_box_collider(floor, 10.0, 0.5, 10.0)
val ball = make_node(1)
world.add_dynamic_body(ball, 0.0, 2.0, 0.0, 1.0)
world.add_sphere_collider(ball, 0.5)
var step = 0
while step < 200:
    world.step(0.016)
    step = step + 1
val pos = world.get_position(ball)
expect(pos.y > -1.0).to_equal(true)
world.destroy()
```

</details>

#### get_all_dynamic_transforms returns only dynamic

1. var world = PhysicsWorld3D create
2. world add static body
3. world add dynamic body
4. world add dynamic body
   - Expected: transforms.len() equals `2`
5. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
world.add_static_body(make_node(0), 0.0, 0.0, 0.0)
world.add_dynamic_body(make_node(1), 1.0, 1.0, 1.0, 1.0)
world.add_dynamic_body(make_node(2), 2.0, 2.0, 2.0, 2.0)
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
| Source | `test/01_unit/lib/engine/physics/physics2/world3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- PhysicsWorld3D

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
