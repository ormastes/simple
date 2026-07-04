# Raycast Specification

> <details>

<!-- sdn-diagram:id=raycast_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=raycast_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

raycast_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=raycast_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Raycast Specification

## Scenarios

### Raycast2D

#### hits a box collider

- var world = PhysicsWorld2D create
- world add static body
- world add box collider
   - Expected: hit.has_hit is true
   - Expected: hit.distance > 3.5 is true
   - Expected: hit.distance < 4.5 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_static_body(node, 5.0, 0.0)
world.add_box_collider(node, 1.0, 1.0)
val hit = raycast_2d(0.0, 0.0, 1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance > 3.5).to_equal(true)
expect(hit.distance < 4.5).to_equal(true)
world.destroy()
```

</details>

#### misses when ray points away

- var world = PhysicsWorld2D create
- world add static body
- world add box collider
   - Expected: hit.has_hit is false
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_static_body(node, 5.0, 0.0)
world.add_box_collider(node, 1.0, 1.0)
val hit = raycast_2d(0.0, 0.0, -1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(false)
world.destroy()
```

</details>

#### hits circle collider

- var world = PhysicsWorld2D create
- world add static body
- world add circle collider
   - Expected: hit.has_hit is true
   - Expected: hit.distance > 3.5 is true
   - Expected: hit.distance < 4.5 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
val node = make_node(1)
world.add_static_body(node, 0.0, 5.0)
world.add_circle_collider(node, 1.0)
val hit = raycast_2d(0.0, 0.0, 0.0, 1.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance > 3.5).to_equal(true)
expect(hit.distance < 4.5).to_equal(true)
world.destroy()
```

</details>

#### returns closest hit

- var world = PhysicsWorld2D create
- world add static body
- world add box collider
- world add static body
- world add box collider
   - Expected: hit.has_hit is true
   - Expected: hit.distance < 6.0 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_2d()
var world = PhysicsWorld2D.create(config)
world.add_static_body(make_node(1), 5.0, 0.0)
world.add_box_collider(make_node(1), 0.5, 0.5)
world.add_static_body(make_node(2), 10.0, 0.0)
world.add_box_collider(make_node(2), 0.5, 0.5)
val hit = raycast_2d(0.0, 0.0, 1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance < 6.0).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/engine/physics/physics2/raycast_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Raycast2D

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
