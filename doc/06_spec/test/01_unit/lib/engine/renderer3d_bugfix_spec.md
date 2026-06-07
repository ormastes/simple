# renderer3d_bugfix_spec

> Engine Renderer3D Bug Fix — ForwardRenderer3D regression tests

<!-- sdn-diagram:id=renderer3d_bugfix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderer3d_bugfix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderer3d_bugfix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderer3d_bugfix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# renderer3d_bugfix_spec

Engine Renderer3D Bug Fix — ForwardRenderer3D regression tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/renderer3d_bugfix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Renderer3D Bug Fix — ForwardRenderer3D regression tests

Tests that node positioning affects rendered output, verifies renderer
creation dimensions, and checks that empty scenes produce clear color only.

## Scenarios

### ForwardRenderer3D

#### creates with correct dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = ForwardRenderer3D.create(160, 120)
expect(renderer.width).to_equal(160)
expect(renderer.height).to_equal(120)
val pixels = renderer.get_pixels()
# Pixel buffer should be width * height
expect(pixels.len()).to_equal(19200)
```

</details>

#### render_scene with empty scene produces clear color only

1. var nodes = NodeStore3D create
2. var components = ComponentRegistry3D create
3. var renderer = ForwardRenderer3D create
4. nodes set position
5. components attach
6. renderer clear
   - Expected: stats.draw_calls equals `0`
   - Expected: stats.triangles equals `0`
   - Expected: pixels.len() equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()
var renderer = ForwardRenderer3D.create(16, 16)
# Create camera only — no meshes
val cam_id = nodes.create_node("camera")
nodes.set_position(cam_id, Vec3(x: 0.0, y: 0.0, z: 5.0))
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
components.attach(cam_id, Component3D.Camera(data: cam))
# Clear and render empty scene
renderer.clear()
val stats = renderer.render_scene(nodes, components, cam_id)
# No draw calls because no meshes
expect(stats.draw_calls).to_equal(0)
expect(stats.triangles).to_equal(0)
# Pixels should still exist (all clear color)
val pixels = renderer.get_pixels()
expect(pixels.len()).to_equal(256)
```

</details>

#### render with positioned node produces different pixels than origin

1. var nodes = NodeStore3D create
2. var components = ComponentRegistry3D create
3. var renderer a = ForwardRenderer3D create
4. var renderer b = ForwardRenderer3D create
5. nodes set position
6. components attach
7. components attach
8. components attach
9. renderer a clear
10. nodes set position
11. renderer b clear
   - Expected: differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var nodes = NodeStore3D.create()
var components = ComponentRegistry3D.create()
var renderer_a = ForwardRenderer3D.create(32, 32)
var renderer_b = ForwardRenderer3D.create(32, 32)
# Camera
val cam_id = nodes.create_node("camera")
nodes.set_position(cam_id, Vec3(x: 0.0, y: 0.0, z: 10.0))
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
components.attach(cam_id, Component3D.Camera(data: cam))
# Light
val light_id = nodes.create_node("light")
val light = directional_light(Vec3(x: 0.0, y: -1.0, z: -1.0), EngineColor.white(), 1.0)
components.attach(light_id, Component3D.Light(data: light))
# Mesh at origin
val mesh_id = nodes.create_node("cube_origin")
val mesh = create_cube(1.0)
val material = unlit_material(EngineColor.red())
components.attach(mesh_id, Component3D.Mesh(mesh: mesh, material: material))
# Render A: mesh at origin
renderer_a.clear()
val stats_a = renderer_a.render_scene(nodes, components, cam_id)
val pixels_a = renderer_a.get_pixels()
# Move mesh off to the side
nodes.set_position(mesh_id, Vec3(x: 5.0, y: 0.0, z: 0.0))
# Render B: mesh displaced
renderer_b.clear()
val stats_b = renderer_b.render_scene(nodes, components, cam_id)
val pixels_b = renderer_b.get_pixels()
# Both should have drawn something
expect(stats_a.draw_calls).to_be_greater_than(0)
expect(stats_b.draw_calls).to_be_greater_than(0)
# Pixels should differ (different positions produce different images)
var differ = false
var i = 0
while i < pixels_a.len():
    if pixels_a[i] != pixels_b[i]:
        differ = true
    i = i + 1
expect(differ).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
