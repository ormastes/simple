# Simple-Native 3D Game Engine — Current API Smoke Specification

> 1. var store = NodeStore3D create

<!-- sdn-diagram:id=engine_3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple-Native 3D Game Engine — Current API Smoke Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/engine_3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Engine3D current API smoke

#### creates 3D scene nodes with valid handles

1. var store = NodeStore3D create
   - Expected: root.is_valid() is true
   - Expected: child.is_valid() is true
   - Expected: store.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = NodeStore3D.create()
val root = store.create_node("root")
val child = store.create_node("child")
expect(root.is_valid()).to_equal(true)
expect(child.is_valid()).to_equal(true)
expect(store.count).to_equal(2)
```

</details>

#### constructs mesh, camera, light, and material components

1. var nodes = NodeStore3D create
2. var components = ComponentRegistry3D create
3. components attach
4. components attach
   - Expected: cam.near_plane equals `0.1`
5. components attach
   - Expected: light.intensity equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()

val mesh_id = nodes.create_node("cube")
val mesh = create_cube(1.0)
val material = pbr_material(EngineColor.red(), 0.0, 0.5)
components.attach(mesh_id, Component3D.Mesh(mesh: mesh, material: material))
expect(mesh.vertex_count()).to_be_greater_than(0)

val cam_id = nodes.create_node("camera")
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.333, 0.1, 100.0)
components.attach(cam_id, Component3D.Camera(data: cam))
expect(cam.near_plane).to_equal(0.1)

val light_id = nodes.create_node("light")
val light = directional_light(Vec3(x: 0.0, y: -1.0, z: 0.0), EngineColor.white(), 1.0)
components.attach(light_id, Component3D.Light(data: light))
expect(light.intensity).to_equal(1.0)
```

</details>

#### creates renderer and primitive mesh resources

1. var renderer = ForwardRenderer3D create
2. renderer clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = ForwardRenderer3D.create(32, 32)
renderer.clear()
val plane = create_plane(2.0, 2.0)
val material = unlit_material(EngineColor.blue())
expect(plane.vertex_count()).to_be_greater_than(0)
expect(material.albedo.b).to_be_greater_than(0.0)
```

</details>

#### creates physics world and clock state

1. var world = PhysicsWorld3D create
   - Expected: world.bodies.len() equals `0`
2. world destroy
3. var clock = Clock create
4. clock tick
5. clock tick


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_physics_config_3d()
var world = PhysicsWorld3D.create(config)
expect(world.bodies.len()).to_equal(0)
world.destroy()

var clock = Clock.create(Seconds(value: 0.016666))
clock.tick(1000000000)
clock.tick(1050000000)
expect(clock.consume_fixed_steps()).to_be_greater_than(0)
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
