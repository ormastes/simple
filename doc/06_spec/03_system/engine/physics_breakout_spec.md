# Physics Breakout Specification

> 1. var world = make breakout world

<!-- sdn-diagram:id=physics_breakout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_breakout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_breakout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_breakout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Physics Breakout Specification

## Scenarios

### Physics2 Breakout System

#### ball moves after launch

1. var world = make breakout world
2. world apply impulse
3. step n
   - Expected: pos.y > 1.5 is true
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_breakout_world()
world.apply_impulse(make_node(0), 2.0, 4.0)
step_n(world, 20)
val pos = world.get_position(make_node(0))
expect(pos.y > 1.5).to_equal(true)
world.destroy()
```

</details>

#### ball stays within world bounds

1. var world = make breakout world
2. world apply impulse
3. step n
   - Expected: pos.x > -6.0 is true
   - Expected: pos.x < 6.0 is true
   - Expected: pos.y < 8.0 is true
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_breakout_world()
world.apply_impulse(make_node(0), 3.0, 4.0)
step_n(world, 80)
val pos = world.get_position(make_node(0))
expect(pos.x > -6.0).to_equal(true)
expect(pos.x < 6.0).to_equal(true)
expect(pos.y < 8.0).to_equal(true)
world.destroy()
```

</details>

#### ball speed approximately preserved

1. var world = make breakout world
2. world apply impulse
3. step n
   - Expected: speed_after > 1.0 is true
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_breakout_world()
world.apply_impulse(make_node(0), 0.5, 4.0)
step_n(world, 30)
val speed_after = get_speed(world)
expect(speed_after > 1.0).to_equal(true)
world.destroy()
```

</details>

#### BVH active with many colliders

1. var world = make breakout world
   - Expected: world.colliders.count > 4 is true
   - Expected: world.use_bvh is true
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var world = make_breakout_world()
expect(world.colliders.count > 4).to_equal(true)
expect(world.use_bvh).to_equal(true)
world.destroy()
```

</details>

#### deterministic simulation

1. var config = default physics config 2d
2. config gravity = Vec2
3. var w1 = PhysicsWorld2D create
4. w1 add dynamic body
5. w1 add circle collider
6. w1 add static body
7. w1 add box collider
8. w1 apply impulse
9. step n
10. w1 destroy
11. var config2 = default physics config 2d
12. config2 gravity = Vec2
13. var w2 = PhysicsWorld2D create
14. w2 add dynamic body
15. w2 add circle collider
16. w2 add static body
17. w2 add box collider
18. w2 apply impulse
19. step n
20. w2 destroy
   - Expected: p1.x equals `p2.x`
   - Expected: p1.y equals `p2.y`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var config = default_physics_config_2d()
config.gravity = Vec2(x: 0.0, y: 0.0)
config.restitution = 1.0
config.friction = 0.0
var w1 = PhysicsWorld2D.create(config)
w1.add_dynamic_body(make_node(0), 0.0, 1.0, 1.0)
w1.add_circle_collider(make_node(0), 0.3)
w1.add_static_body(make_node(100), 0.0, 5.0)
w1.add_box_collider(make_node(100), 3.0, 0.5)
w1.apply_impulse(make_node(0), 1.0, 4.0)
step_n(w1, 50)
val p1 = w1.get_position(make_node(0))
w1.destroy()
var config2 = default_physics_config_2d()
config2.gravity = Vec2(x: 0.0, y: 0.0)
config2.restitution = 1.0
config2.friction = 0.0
var w2 = PhysicsWorld2D.create(config2)
w2.add_dynamic_body(make_node(0), 0.0, 1.0, 1.0)
w2.add_circle_collider(make_node(0), 0.3)
w2.add_static_body(make_node(100), 0.0, 5.0)
w2.add_box_collider(make_node(100), 3.0, 0.5)
w2.apply_impulse(make_node(0), 1.0, 4.0)
step_n(w2, 50)
val p2 = w2.get_position(make_node(0))
w2.destroy()
expect(p1.x).to_equal(p2.x)
expect(p1.y).to_equal(p2.y)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/physics_breakout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Physics2 Breakout System

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
