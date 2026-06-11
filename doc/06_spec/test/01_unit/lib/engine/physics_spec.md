# physics_spec

> Engine Physics — PhysicsWorld2D public API tests

<!-- sdn-diagram:id=physics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=physics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

physics_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=physics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# physics_spec

Engine Physics — PhysicsWorld2D public API tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Physics — PhysicsWorld2D public API tests

Tests physics world creation, body management, stepping, force/impulse
application, transform queries, and body removal. Uses the pure Simple
physics engine via PhysicsWorld2D.

## Scenarios

### PhysicsWorld2D

#### create with default config

1. var world = PhysicsWorld2D create
   - Expected: world.bodies.len() equals `0`
   - Expected: world.colliders.len() equals `0`
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
expect(world.bodies.len()).to_equal(0)
expect(world.colliders.len()).to_equal(0)
world.destroy()
```

</details>

#### add_dynamic_body and get_position returns initial position

1. var world = PhysicsWorld2D create
   - Expected: ok is true
   - Expected: world.bodies.len() equals `1`
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val node_id = NodeId(raw: RawHandle.new(0, 1))
val ok = world.add_dynamic_body(node_id, 10.0, 20.0)
expect(ok).to_equal(true)
expect(world.bodies.len()).to_equal(1)
val pos = world.get_position(node_id)
val px_i = pos.x * 100.0
val py_i = pos.y * 100.0
expect(px_i).to_be_greater_than(999.0)
expect(px_i).to_be_less_than(1001.0)
expect(py_i).to_be_greater_than(1999.0)
expect(py_i).to_be_less_than(2001.0)
world.destroy()
```

</details>

#### add_static_body

1. var world = PhysicsWorld2D create
   - Expected: ok is true
   - Expected: world.bodies.len() equals `1`
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val node_id = NodeId(raw: RawHandle.new(1, 1))
val ok = world.add_static_body(node_id, 0.0, -5.0)
expect(ok).to_equal(true)
expect(world.bodies.len()).to_equal(1)
world.destroy()
```

</details>

#### step does not crash

1. var world = PhysicsWorld2D create
   - Expected: ok is true
2. world step
3. world step
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val node_id = NodeId(raw: RawHandle.new(0, 1))
val ok = world.add_dynamic_body(node_id, 0.0, 10.0)
expect(ok).to_equal(true)
# Step should not panic
world.step(Seconds(value: 0.016666))
world.step(Seconds(value: 0.016666))
world.destroy()
```

</details>

#### apply_force changes velocity

1. var world = PhysicsWorld2D create
   - Expected: ok is true
   - Expected: force_ok is true
2. world step
3. world step
4. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val node_id = NodeId(raw: RawHandle.new(0, 1))
val ok = world.add_dynamic_body(node_id, 0.0, 0.0)
expect(ok).to_equal(true)
val vel_before = world.get_velocity(node_id)
val vbx_i = vel_before.x * 1000.0
expect(vbx_i).to_be_greater_than(-1.0)
expect(vbx_i).to_be_less_than(1.0)
# Apply horizontal force and step
val force_ok = world.apply_force(node_id, Vec2(x: 1000.0, y: 0.0))
expect(force_ok).to_equal(true)
world.step(Seconds(value: 0.016666))
world.step(Seconds(value: 0.016666))
val vel_after = world.get_velocity(node_id)
# Velocity x should have increased from the force
expect(vel_after.x).to_be_greater_than(0.0)
world.destroy()
```

</details>

#### apply_impulse changes position after step

1. var world = PhysicsWorld2D create
   - Expected: ok is true
   - Expected: impulse_ok is true
2. world step
3. world step
4. world step
5. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val node_id = NodeId(raw: RawHandle.new(0, 1))
val ok = world.add_dynamic_body(node_id, 0.0, 0.0)
expect(ok).to_equal(true)
val pos_before = world.get_position(node_id)
# Apply a strong horizontal impulse
val impulse_ok = world.apply_impulse(node_id, Vec2(x: 50.0, y: 0.0))
expect(impulse_ok).to_equal(true)
# Step multiple times to let the body move
world.step(Seconds(value: 0.016666))
world.step(Seconds(value: 0.016666))
world.step(Seconds(value: 0.016666))
val pos_after = world.get_position(node_id)
# X position should have increased
expect(pos_after.x).to_be_greater_than(pos_before.x)
world.destroy()
```

</details>

#### get_all_dynamic_transforms returns entries

1. var world = PhysicsWorld2D create
   - Expected: ok1 is true
   - Expected: ok2 is true
   - Expected: transforms.len() equals `2`
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val n1 = NodeId(raw: RawHandle.new(0, 1))
val n2 = NodeId(raw: RawHandle.new(1, 1))
val ok1 = world.add_dynamic_body(n1, 0.0, 0.0)
val ok2 = world.add_dynamic_body(n2, 5.0, 5.0)
expect(ok1).to_equal(true)
expect(ok2).to_equal(true)
val transforms = world.get_all_dynamic_transforms()
expect(transforms.len()).to_equal(2)
world.destroy()
```

</details>

#### remove_body removes the body

1. var world = PhysicsWorld2D create
   - Expected: ok is true
   - Expected: world.bodies.len() equals `1`
   - Expected: removed is true
   - Expected: world.bodies.len() equals `0`
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val node_id = NodeId(raw: RawHandle.new(0, 1))
val ok = world.add_dynamic_body(node_id, 0.0, 0.0)
expect(ok).to_equal(true)
expect(world.bodies.len()).to_equal(1)
val removed = world.remove_body(node_id)
expect(removed).to_equal(true)
expect(world.bodies.len()).to_equal(0)
world.destroy()
```

</details>

#### get_position returns zero for unknown node

1. var world = PhysicsWorld2D create
2. world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config()
var world = PhysicsWorld2D.create(config)
val unknown = NodeId(raw: RawHandle.new(99, 1))
val pos = world.get_position(unknown)
val px_i = pos.x * 1000.0
val py_i = pos.y * 1000.0
expect(px_i).to_be_greater_than(-1.0)
expect(px_i).to_be_less_than(1.0)
expect(py_i).to_be_greater_than(-1.0)
expect(py_i).to_be_less_than(1.0)
world.destroy()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
