# Mesh Specification

> <details>

<!-- sdn-diagram:id=mesh_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mesh_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mesh_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mesh_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mesh Specification

## Scenarios

### Vertex3D

#### creates with position and normal

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = Vec3(x: 1.0, y: 2.0, z: 3.0)
val norm = Vec3(x: 0.0, y: 1.0, z: 0.0)
val v = Vertex3D.create(pos, norm, 0.5, 0.5)
expect(v.position.x).to_equal(1.0)
expect(v.position.y).to_equal(2.0)
expect(v.position.z).to_equal(3.0)
expect(v.normal.y).to_equal(1.0)
expect(v.uv_x).to_equal(0.5)
expect(v.uv_y).to_equal(0.5)
```

</details>

#### creates with color

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val norm = Vec3(x: 0.0, y: 0.0, z: 1.0)
val red = EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val v = Vertex3D.with_color(pos, norm, 0.0, 0.0, red)
expect(v.color.r).to_equal(1.0)
expect(v.color.g).to_equal(0.0)
expect(v.color.b).to_equal(0.0)
```

</details>

#### defaults to white color

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val norm = Vec3(x: 0.0, y: 1.0, z: 0.0)
val v = Vertex3D.create(pos, norm, 0.0, 0.0)
expect(v.color.r).to_equal(1.0)
expect(v.color.g).to_equal(1.0)
expect(v.color.b).to_equal(1.0)
expect(v.color.a).to_equal(1.0)
```

</details>

### MeshData

#### reports vertex and index counts

1. aabb min: Vec3 zero
2. aabb max: Vec3
   - Expected: mesh.vertex_count() equals `3`
   - Expected: mesh.index_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val norm = Vec3(x: 0.0, y: 1.0, z: 0.0)
val v0 = Vertex3D.create(pos, norm, 0.0, 0.0)
val v1 = Vertex3D.create(Vec3(x: 1.0, y: 0.0, z: 0.0), norm, 1.0, 0.0)
val v2 = Vertex3D.create(Vec3(x: 0.0, y: 0.0, z: 1.0), norm, 0.0, 1.0)
val mesh = MeshData(
    vertices: [v0, v1, v2],
    indices: [0, 1, 2],
    aabb_min: Vec3.zero(),
    aabb_max: Vec3(x: 1.0, y: 0.0, z: 1.0)
)
expect(mesh.vertex_count()).to_equal(3)
expect(mesh.index_count()).to_equal(3)
```

</details>

### create_cube

#### generates correct vertex count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cube = create_cube(1.0)
# Cube: 6 faces * 4 vertices = 24
expect(cube.vertex_count()).to_equal(24)
```

</details>

#### generates correct index count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cube = create_cube(1.0)
# Cube: 6 faces * 2 triangles * 3 indices = 36
expect(cube.index_count()).to_equal(36)
```

</details>

#### has valid AABB for unit cube

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cube = create_cube(2.0)
# Half-size should be 1.0 for a size-2 cube
expect(cube.aabb_max.x).to_equal(1.0)
expect(cube.aabb_min.x).to_equal(-1.0)
expect(cube.aabb_max.y).to_equal(1.0)
expect(cube.aabb_min.y).to_equal(-1.0)
```

</details>

### create_plane

#### generates 4 vertices and 6 indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plane = create_plane(2.0, 2.0)
expect(plane.vertex_count()).to_equal(4)
expect(plane.index_count()).to_equal(6)
```

</details>

#### has correct AABB

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plane = create_plane(4.0, 2.0)
expect(plane.aabb_max.x).to_equal(2.0)
expect(plane.aabb_min.x).to_equal(-2.0)
expect(plane.aabb_max.z).to_equal(1.0)
expect(plane.aabb_min.z).to_equal(-1.0)
```

</details>

### create_sphere

#### generates vertices for given segments and rings

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sphere = create_sphere(1.0, 8, 6)
# Sphere vertex count: (segments+1) * (rings+1) = 9 * 7 = 63
expect(sphere.vertex_count()).to_equal(63)
# Sphere index count: segments * rings * 6 = 8 * 6 * 6 = 288
expect(sphere.index_count()).to_equal(288)
```

</details>

#### has positive vertex and index counts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sphere = create_sphere(1.0, 4, 3)
expect(sphere.vertex_count()).to_be_greater_than(0)
expect(sphere.index_count()).to_be_greater_than(0)
```

</details>

### compute_aabb

#### computes tight bounding box for plane

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plane = create_plane(4.0, 2.0)
val aabb = compute_aabb(plane)
expect(aabb.aabb_max.x).to_equal(2.0)
expect(aabb.aabb_min.x).to_equal(-2.0)
expect(aabb.aabb_max.z).to_equal(1.0)
expect(aabb.aabb_min.z).to_equal(-1.0)
```

</details>

#### handles empty mesh

1. aabb min: Vec3 zero
2. aabb max: Vec3 zero
   - Expected: result.aabb_min.x equals `0.0`
   - Expected: result.aabb_max.x equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = MeshData(
    vertices: [],
    indices: [],
    aabb_min: Vec3.zero(),
    aabb_max: Vec3.zero()
)
val result = compute_aabb(empty)
expect(result.aabb_min.x).to_equal(0.0)
expect(result.aabb_max.x).to_equal(0.0)
```

</details>

### directional_light

#### creates with direction and intensity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = Vec3(x: 0.0, y: -1.0, z: 0.0)
val white = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val light = directional_light(dir, white, 2.0)
expect(light.light_type).to_equal(0)
expect(light.intensity).to_equal(2.0)
expect(light.color.r).to_equal(1.0)
```

</details>

#### normalizes direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = Vec3(x: 0.0, y: -1.0, z: 0.0)
val white = EngineColor.white()
val light = directional_light(dir, white, 1.0)
expect(light.direction.y).to_equal(-1.0)
```

</details>

### point_light

#### creates with range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val light = point_light(white, 1.5, 10.0)
expect(light.light_type).to_equal(1)
expect(light.intensity).to_equal(1.5)
expect(light.range).to_equal(10.0)
```

</details>

#### has zero direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
val light = point_light(white, 1.0, 5.0)
expect(light.direction.x).to_equal(0.0)
expect(light.direction.y).to_equal(0.0)
expect(light.direction.z).to_equal(0.0)
```

</details>

### spot_light

#### creates with cone angles

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = Vec3(x: 0.0, y: -1.0, z: 0.0)
val white = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val light = spot_light(dir, white, 1.0, 5.0, 0.5, 0.8)
expect(light.light_type).to_equal(2)
expect(light.inner_cone).to_equal(0.5)
expect(light.outer_cone).to_equal(0.8)
expect(light.range).to_equal(5.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/mesh_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Vertex3D
- MeshData
- create_cube
- create_plane
- create_sphere
- compute_aabb
- directional_light
- point_light
- spot_light

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
