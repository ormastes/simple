# Renderer3d Specification

> <details>

<!-- sdn-diagram:id=renderer3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=renderer3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

renderer3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=renderer3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Renderer3d Specification

## Scenarios

### Camera3DData

#### creates perspective camera

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.333, 0.1, 100.0)
expect(cam.is_active).to_equal(true)
expect(cam.is_orthographic).to_equal(false)
expect(cam.near_plane).to_equal(0.1)
expect(cam.far_plane).to_equal(100.0)
```

</details>

#### creates orthographic camera

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera3DData.orthographic(5.0, 1.5, 0.1, 50.0)
expect(cam.is_orthographic).to_equal(true)
expect(cam.ortho_size).to_equal(5.0)
```

</details>

<details>
<summary>Advanced: generates projection matrix</summary>

#### generates projection matrix

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
val proj = cam.projection_matrix()
# Projection matrix should be non-identity (element [0][0] != 1.0 for perspective)
val m00 = proj.get(0, 0)
expect(m00).to_be_greater_than(0.0)
```

</details>


</details>

<details>
<summary>Advanced: generates view matrix from transform</summary>

#### generates view matrix from transform

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
val transform = Transform3D.identity()
val view = cam.view_matrix(transform)
# At identity transform, view should be a look_at from origin
val m33 = view.get(3, 3)
expect(m33).to_equal(1.0)
```

</details>


</details>

### ComponentRegistry3D

#### attaches and retrieves mesh component

1. var reg = ComponentRegistry3D create
2. reg attach
   - Expected: components.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry3D.create()
val nid = NodeId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val mesh = create_cube(1.0)
val mat = unlit_material(EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0))
reg.attach(nid, Component3D.Mesh(mesh: mesh, material: mat))
val components = reg.get_components(nid)
expect(components.len()).to_equal(1)
```

</details>

#### attaches light component

1. var reg = ComponentRegistry3D create
2. reg attach
   - Expected: ld.intensity equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry3D.create()
val nid = NodeId(raw: RawHandle(index: 1, generation: Generation(value: 1)))
val dir = Vec3(x: 0.0, y: -1.0, z: 0.0)
val light = directional_light(dir, EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0), 1.0)
reg.attach(nid, Component3D.Light(data: light))
val maybe_light = reg.get_light(nid)
if val Some(ld) = maybe_light:
    expect(ld.intensity).to_equal(1.0)
```

</details>

#### attaches camera component

1. var reg = ComponentRegistry3D create
2. reg attach
   - Expected: cd.near_plane equals `0.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry3D.create()
val nid = NodeId(raw: RawHandle(index: 2, generation: Generation(value: 1)))
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
reg.attach(nid, Component3D.Camera(data: cam))
val maybe_cam = reg.get_camera(nid)
if val Some(cd) = maybe_cam:
    expect(cd.near_plane).to_equal(0.1)
```

</details>

#### detaches all components

1. var reg = ComponentRegistry3D create
2. reg attach
3. reg detach all
   - Expected: components.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reg = ComponentRegistry3D.create()
val nid = NodeId(raw: RawHandle(index: 0, generation: Generation(value: 1)))
val mesh = create_cube(1.0)
val mat = unlit_material(EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
reg.attach(nid, Component3D.Mesh(mesh: mesh, material: mat))
reg.detach_all(nid)
val components = reg.get_components(nid)
expect(components.len()).to_equal(0)
```

</details>

#### returns empty for unknown node

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reg = ComponentRegistry3D.create()
val nid = NodeId(raw: RawHandle(index: 99, generation: Generation(value: 1)))
val components = reg.get_components(nid)
expect(components.len()).to_equal(0)
```

</details>

#### identifies component types

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mesh = create_cube(1.0)
val mat = unlit_material(EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0))
val comp = Component3D.Mesh(mesh: mesh, material: mat)
expect(comp.is_mesh()).to_equal(true)
expect(comp.is_light()).to_equal(false)
expect(comp.type_name()).to_equal("Mesh")
```

</details>

### ForwardRenderer3D

#### creates with dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = ForwardRenderer3D.create(8, 6)
expect(renderer.width).to_equal(8)
expect(renderer.height).to_equal(6)
expect(renderer.pixels.len()).to_equal(48)
expect(renderer.depth.len()).to_equal(48)
```

</details>

#### clears pixel and depth buffers

1. var renderer = ForwardRenderer3D create
2. renderer clear
   - Expected: renderer.depth[0] equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = ForwardRenderer3D.create(4, 4)
renderer.clear()
# Depth should be 1.0 (far plane)
expect(renderer.depth[0]).to_equal(1.0)
```

</details>

#### resizes buffers

1. var renderer = ForwardRenderer3D create
2. renderer resize
   - Expected: renderer.width equals `8`
   - Expected: renderer.pixels.len() equals `64`
   - Expected: renderer.depth.len() equals `64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = ForwardRenderer3D.create(4, 4)
renderer.resize(8, 8)
expect(renderer.width).to_equal(8)
expect(renderer.pixels.len()).to_equal(64)
expect(renderer.depth.len()).to_equal(64)
```

</details>

#### renders scene with camera and mesh

1. var renderer = ForwardRenderer3D create
2. renderer clear
3. var nodes = NodeStore3D create
4. var reg = ComponentRegistry3D create
5. nodes set position
6. reg attach
7. reg attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var renderer = ForwardRenderer3D.create(8, 8)
renderer.clear()
var nodes = NodeStore3D.create()
var reg = ComponentRegistry3D.create()
# Create camera node
val cam_id = nodes.create_node("camera")
nodes.set_position(cam_id, Vec3(x: 0.0, y: 0.0, z: 5.0))
val cam = Camera3DData.perspective(Angle(radians: 1.0), 1.0, 0.1, 100.0)
reg.attach(cam_id, Component3D.Camera(data: cam))
# Create mesh node
val mesh_id = nodes.create_node("cube")
val mesh = create_cube(1.0)
val mat = unlit_material(EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0))
reg.attach(mesh_id, Component3D.Mesh(mesh: mesh, material: mat))
# Render
val stats = renderer.render_scene(nodes, reg, cam_id)
expect(stats.draw_calls).to_be_greater_than(0)
```

</details>

### ScreenVertex

#### creates with fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sv = ScreenVertex(sx: 100.0, sy: 200.0, depth: 0.5, color: EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0))
expect(sv.sx).to_equal(100.0)
expect(sv.depth).to_equal(0.5)
```

</details>

### LightInstance

#### creates with light data

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = Vec3(x: 0.0, y: -1.0, z: 0.0)
val light = directional_light(dir, EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0), 1.0)
val li = LightInstance(data: light, world_position: Vec3.zero(), world_direction: dir)
expect(li.data.intensity).to_equal(1.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/renderer3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Camera3DData
- ComponentRegistry3D
- ForwardRenderer3D
- ScreenVertex
- LightInstance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
