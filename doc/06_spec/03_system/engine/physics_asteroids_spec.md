# Physics Asteroids Specification

> 1. var world = make asteroid field

<!-- sdn-diagram:id=physics_asteroids_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_asteroids_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_asteroids_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_asteroids_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Asteroids Specification

## Scenarios

### Physics2 Asteroids System

#### many bodies simulate without explosion

1. var world = make asteroid field
2. step n
   - Expected: all_bounded is true
3. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_asteroid_field(20)
step_n(world, 30)
var all_bounded = true
var i = 0
while i < 20:
    val pos = world.get_position(make_node(i))
    if pos.x < -50.0 or pos.x > 50.0:
        all_bounded = false
    if pos.y < -50.0 or pos.y > 50.0:
        all_bounded = false
    i = i + 1
expect(all_bounded).to_equal(true)
world.destroy()
```

</details>

#### BVH used for many colliders

1. var world = make asteroid field
   - Expected: world.colliders.count > 4 is true
   - Expected: world.use_bvh is true
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_asteroid_field(10)
expect(world.colliders.count > 4).to_equal(true)
expect(world.use_bvh).to_equal(true)
world.destroy()
```

</details>

#### raycast hits nearest body

1. var config = default physics config 2d
2. config gravity = Vec2
3. var world = PhysicsWorld2D create
4. world add static body
5. world add circle collider
6. world add static body
7. world add circle collider
   - Expected: hit.has_hit is true
   - Expected: hit.distance < 5.0 is true
8. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
var world = PhysicsWorld2D.create(config)
world.add_static_body(make_node(0), 5.0, 0.0)
world.add_circle_collider(make_node(0), 1.0)
world.add_static_body(make_node(1), 10.0, 0.0)
world.add_circle_collider(make_node(1), 1.0)
val hit = raycast_2d(0.0, 0.0, 1.0, 0.0, 100.0, world.bodies, world.colliders)
expect(hit.has_hit).to_equal(true)
expect(hit.distance < 5.0).to_equal(true)
world.destroy()
```

</details>

#### overlap query finds bodies in radius

1. var config = default physics config 2d
2. config gravity = Vec2
3. var world = PhysicsWorld2D create
4. world add static body
5. world add circle collider
6. world add static body
7. world add circle collider
   - Expected: results.len() > 0 is true
8. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
var world = PhysicsWorld2D.create(config)
world.add_static_body(make_node(0), 2.0, 0.0)
world.add_circle_collider(make_node(0), 0.5)
world.add_static_body(make_node(1), 10.0, 0.0)
world.add_circle_collider(make_node(1), 0.5)
val results = circle_overlap_2d(0.0, 0.0, 3.0, world.bodies, world.colliders)
expect(results.len() > 0).to_equal(true)
world.destroy()
```

</details>

#### body count tracks correctly

1. var world = make asteroid field
   - Expected: world.body_count() == 15 is true
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_asteroid_field(15)
expect(world.body_count() == 15).to_equal(true)
world.destroy()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_asteroids_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 Asteroids System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
