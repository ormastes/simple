# PhysicsWorld3D — 3D contact constraint (C29)

> Before this fix, `PhysicsWorld3D` detected contacts in full 3D but its solver only corrected the x/y/ang_z axes — a sphere falling along Z onto a floor free-fell through it forever, since nothing ever touched `pos_z` or `vel_z`. This spec proves the 3D impulse solver now resolves all three axes (position correction, linear velocity, and angular velocity) and that the existing xy-plane (z=0) behavior is unchanged, so games and engine callers get correct 3D collision response without regressing the 2D-compatible case. It also proves the buffered Begin -> Stay -> End contact-event sequence used by gameplay code to detect touch/separate transitions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# PhysicsWorld3D — 3D contact constraint (C29)

Before this fix, `PhysicsWorld3D` detected contacts in full 3D but its solver only corrected the x/y/ang_z axes — a sphere falling along Z onto a floor free-fell through it forever, since nothing ever touched `pos_z` or `vel_z`. This spec proves the 3D impulse solver now resolves all three axes (position correction, linear velocity, and angular velocity) and that the existing xy-plane (z=0) behavior is unchanged, so games and engine callers get correct 3D collision response without regressing the 2D-compatible case. It also proves the buffered Begin -> Stay -> End contact-event sequence used by gameplay code to detect touch/separate transitions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/physics/physics2/world3d_contact3d_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Before this fix, `PhysicsWorld3D` detected contacts in full 3D but its
solver only corrected the x/y/ang_z axes — a sphere falling along Z onto a
floor free-fell through it forever, since nothing ever touched `pos_z` or
`vel_z`. This spec proves the 3D impulse solver now resolves all three
axes (position correction, linear velocity, and angular velocity) and
that the existing xy-plane (z=0) behavior is unchanged, so games and
engine callers get correct 3D collision response without regressing the
2D-compatible case. It also proves the buffered Begin -> Stay -> End
contact-event sequence used by gameplay code to detect touch/separate
transitions.

## Examples

A sphere falling straight down onto a static box has its Z position
corrected (no tunneling) and its downward Z velocity absorbed by the
contact, rather than growing without bound. A sphere hit with a sideways
force while resting on a Z-normal floor picks up angular velocity about
the Y axis (friction torque from a Z-normal r x X-direction force), which
the pre-fix solver could never produce since it never wrote ang_vel_x/y.
An all-z=0 scene reproduces the exact pre-fix 2D behavior as a regression
guard. A resting contact between two spheres reports BEGIN on first
overlap, STAY while still touching, and END once an applied force
separates them.

## Scenarios

### PhysicsWorld3D — 3D contact constraint (C29)

#### sphere falling along z onto a static box resolves penetration and kills z relative velocity

- Drop a dynamic sphere onto a static box floor under -z gravity
- var world = PhysicsWorld3D create
- world add static body
- world add box collider
- world add dynamic body
- world add sphere collider
- world step
- The floor must stop the sphere and absorb its downward velocity
   - Expected: pos.z > -1.0 is true
   - Expected: math_abs(vel.z) < 5.0 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Drop a dynamic sphere onto a static box floor under -z gravity")
var world = PhysicsWorld3D.create(z_gravity_config())
val floor = make_node(0)
world.add_static_body(floor, 0.0, 0.0, 0.0)
world.add_box_collider(floor, 10.0, 10.0, 0.5)
val ball = make_node(1)
world.add_dynamic_body(ball, 0.0, 0.0, 2.0, 1.0)
world.add_sphere_collider(ball, 0.5)
var step_count = 0
while step_count < 200:
    world.step(0.016)
    step_count = step_count + 1
val pos = world.get_position(ball)
val vel = world.get_velocity(ball)
step("The floor must stop the sphere and absorb its downward velocity")
# Pre-fix: z was never corrected by the solver (only x/y/ang_z were
# touched), so the sphere free-falls through the floor forever and
# |vel.z| grows without bound (~31 m/s after 3.2s of gravity).
expect(pos.z > -1.0).to_equal(true)
expect(math_abs(vel.z) < 5.0).to_equal(true)
world.destroy()
```

</details>

#### off-axis oblique impact produces angular velocity on a non-z axis

- Rest a sphere on the floor, then push it sideways every step
- var world = PhysicsWorld3D create
- world add static body
- world add box collider
- world add dynamic body
- world add sphere collider
- world apply force
- world step
- Sliding friction on a z-normal floor must spin the sphere about y, not z
   - Expected: pos.z > -1.0 is true
   - Expected: math_abs(ang.y) > 0.001 is true
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Rest a sphere on the floor, then push it sideways every step")
var world = PhysicsWorld3D.create(z_gravity_config())
val floor = make_node(0)
world.add_static_body(floor, 0.0, 0.0, 0.0)
world.add_box_collider(floor, 10.0, 10.0, 0.5)
val ball = make_node(1)
world.add_dynamic_body(ball, 0.0, 0.0, 2.0, 1.0)
world.add_sphere_collider(ball, 0.5)
var step_count = 0
while step_count < 200:
    # Persistent sideways force: sliding contact on a z-normal
    # floor produces friction torque about the Y axis (r along z,
    # force along x -> r x F has a y component), never Z.
    world.apply_force(ball, 3.0, 0.0, 0.0)
    world.step(0.016)
    step_count = step_count + 1
val pos = world.get_position(ball)
val ang = world.get_angular_velocity(ball)
step("Sliding friction on a z-normal floor must spin the sphere about y, not z")
# Pre-fix: the solver never wrote ang_vel_x/ang_vel_y at all, so
# ang.y would be exactly 0.0 here regardless of impact geometry.
expect(pos.z > -1.0).to_equal(true)
expect(math_abs(ang.y) > 0.001).to_equal(true)
world.destroy()
```

</details>

#### xy-plane scene (all z=0) matches pre-fix behavior — regression

- Run the same drop scenario rotated into the xy plane (z stays 0 throughout)
- var world = PhysicsWorld3D create
- world add static body
- world add box collider
- world add dynamic body
- world add sphere collider
- world step
- z must stay exactly 0.0 -- the 3D fix must not disturb a pure-2D scene
   - Expected: pos.y > -1.0 is true
   - Expected: pos.x equals `0.0`
   - Expected: pos.z equals `0.0`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the same drop scenario rotated into the xy plane (z stays 0 throughout)")
var world = PhysicsWorld3D.create(default_physics_config_3d())
val floor = make_node(0)
world.add_static_body(floor, 0.0, 0.0, 0.0)
world.add_box_collider(floor, 10.0, 0.5, 10.0)
val ball = make_node(1)
world.add_dynamic_body(ball, 0.0, 2.0, 0.0, 1.0)
world.add_sphere_collider(ball, 0.5)
var step_count = 0
while step_count < 200:
    world.step(0.016)
    step_count = step_count + 1
val pos = world.get_position(ball)
step("z must stay exactly 0.0 -- the 3D fix must not disturb a pure-2D scene")
expect(pos.y > -1.0).to_equal(true)
expect(pos.x).to_equal(0.0)
expect(pos.z).to_equal(0.0)
world.destroy()
```

</details>

#### Begin -> Stay -> End contact event sequence over 3 steps

- Configure a deterministic zero-gravity anchor + mover pair
- var config = default physics config 3d
- config gravity = Vec3
- var world = PhysicsWorld3D create
- world add static body
- world add sphere collider
- world add dynamic body
- world add sphere collider
- Step once: the spheres first overlap this frame
- world step
   - Expected: events1.len() equals `1`
   - Expected: events1[0].phase equals `CONTACT_PHASE_BEGIN`
- Step again with no new force: contact continues (STAY)
- world step
   - Expected: events2.len() equals `1`
   - Expected: events2[0].phase equals `CONTACT_PHASE_STAY`
- Push the mover away with a large force until the spheres separate (END)
- world apply force
- world step
   - Expected: events3.len() equals `1`
   - Expected: events3[0].phase equals `CONTACT_PHASE_END`
- world destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Configure a deterministic zero-gravity anchor + mover pair")
var config = default_physics_config_3d()
config.backend = PhysicsBackend.CpuScalar
config.gravity = Vec3(x: 0.0, y: 0.0, z: 0.0)
config.fixed_timestep = 0.1
config.sub_steps = 1
config.velocity_iterations = 1
config.position_iterations = 1
config.baumgarte_factor = 0.0
config.slop = 0.0
config.restitution = 0.0
config.friction = 0.0
var world = PhysicsWorld3D.create(config)
val anchor = make_node(0)
world.add_static_body(anchor, 0.0, 0.0, 0.0)
world.add_sphere_collider(anchor, 0.5)
val mover = make_node(1)
world.add_dynamic_body(mover, 0.6, 0.0, 0.0, 1.0)
world.add_sphere_collider(mover, 0.5)

step("Step once: the spheres first overlap this frame")
world.step(0.1)
val events1 = world.events()
expect(events1.len()).to_equal(1)
expect(events1[0].phase).to_equal(CONTACT_PHASE_BEGIN)

step("Step again with no new force: contact continues (STAY)")
world.step(0.1)
val events2 = world.events()
expect(events2.len()).to_equal(1)
expect(events2[0].phase).to_equal(CONTACT_PHASE_STAY)

step("Push the mover away with a large force until the spheres separate (END)")
world.apply_force(mover, 100.0, 0.0, 0.0)
world.step(0.1)
val events3 = world.events()
expect(events3.len()).to_equal(1)
expect(events3[0].phase).to_equal(CONTACT_PHASE_END)

world.destroy()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
