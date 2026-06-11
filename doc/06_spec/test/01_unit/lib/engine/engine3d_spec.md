# engine3d_spec

> Engine3D — Facade integration tests

<!-- sdn-diagram:id=engine3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# engine3d_spec

Engine3D — Facade integration tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/engine3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine3D — Facade integration tests

Tests Engine3D creation, node management, component attachment,
physics stepping, and renderer output.

## Scenarios

### Engine3D

#### create initializes all subsystems

1. var nodes = NodeStore3D create
2. var components = ComponentRegistry3D create
3. var physics = PhysicsWorld3D create
4. var renderer = ForwardRenderer3D create
   - Expected: nodes.node_count() equals `0`
   - Expected: physics.bodies.len() equals `0`
   - Expected: renderer.width equals `320`
   - Expected: renderer.height equals `240`
5. physics destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()
val config = default_physics_config_3d()
var physics = PhysicsWorld3D.create(config)
var renderer = ForwardRenderer3D.create(320, 240)
# All subsystems should start empty
expect(nodes.node_count()).to_equal(0)
expect(physics.bodies.len()).to_equal(0)
expect(renderer.width).to_equal(320)
expect(renderer.height).to_equal(240)
physics.destroy()
```

</details>

#### create_node returns valid id

1. var nodes = NodeStore3D create
   - Expected: node.name equals `player`
   - Expected: "node not found" equals `found`
   - Expected: nodes.node_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nodes = NodeStore3D.create()
val node_id = nodes.create_node("player")
val maybe_node = nodes.get_node(node_id)
if val Some(node) = maybe_node:
    expect(node.name).to_equal("player")
else:
    expect("node not found").to_equal("found")
expect(nodes.node_count()).to_equal(1)
```

</details>

#### attach mesh component and retrieve

1. var nodes = NodeStore3D create
2. var components = ComponentRegistry3D create
3. components attach
   - Expected: mesh_data.vertex_count() equals `24`
   - Expected: "mesh not found" equals `found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()
val node_id = nodes.create_node("cube")
val mesh = create_cube(1.0)
val material = unlit_material(EngineColor.red())
components.attach(node_id, Component3D.Mesh(mesh: mesh, material: material))
val retrieved = components.get_mesh(node_id)
if val Some(pair) = retrieved:
    val mesh_data = pair.0
    # Cube has 24 vertices
    expect(mesh_data.vertex_count()).to_equal(24)
else:
    expect("mesh not found").to_equal("found")
```

</details>

#### physics step does not crash

1. var physics = PhysicsWorld3D create
2. physics add dynamic body
3. physics add sphere collider
4. physics step
5. physics step
6. physics destroy


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_3d()
var physics = PhysicsWorld3D.create(config)
val node_id = NodeId(raw: RawHandle.new(0, 1))
physics.add_dynamic_body(node_id, 0.0, 10.0, 0.0)
physics.add_sphere_collider(node_id, 0.5)
physics.step(Seconds(value: 0.016666))
physics.step(Seconds(value: 0.016666))
val pos = physics.get_position(node_id)
# Body should have fallen
expect(pos.y).to_be_less_than(10.0)
physics.destroy()
```

</details>

#### renderer produces pixels after render_scene

1. var nodes = NodeStore3D create
2. var components = ComponentRegistry3D create
3. var renderer = ForwardRenderer3D create
4. nodes set position
5. components attach
6. components attach
7. components attach
8. renderer clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()
var renderer = ForwardRenderer3D.create(64, 64)
# Create camera node
val cam_id = nodes.create_node("camera")
nodes.set_position(cam_id, Vec3(x: 0.0, y: 0.0, z: 5.0))
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
components.attach(cam_id, Component3D.Camera(data: cam))
# Create light node
val light_id = nodes.create_node("light")
val light = directional_light(Vec3(x: 0.0, y: -1.0, z: 0.0), EngineColor.white(), 1.0)
components.attach(light_id, Component3D.Light(data: light))
# Create mesh node
val mesh_id = nodes.create_node("cube")
val mesh = create_cube(1.0)
val material = pbr_material(EngineColor.red(), 0.0, 0.5)
components.attach(mesh_id, Component3D.Mesh(mesh: mesh, material: material))
# Render
renderer.clear()
val stats = renderer.render_scene(nodes, components, cam_id)
val pixels = renderer.get_pixels()
expect(pixels.len()).to_be_greater_than(0)
expect(stats.draw_calls).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
