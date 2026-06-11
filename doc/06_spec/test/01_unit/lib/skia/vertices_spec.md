# SkVertices Specification

> Tests for SkVertices and SkVerticesBuilder — Skia's immutable triangle-mesh primitive consumed by Canvas.drawVertices. Covers builder construction, per-mode triangle counting, bounds computation, and the convenience sk_vertices_triangles factory.

<!-- sdn-diagram:id=vertices_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vertices_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vertices_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vertices_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SkVertices Specification

Tests for SkVertices and SkVerticesBuilder — Skia's immutable triangle-mesh primitive consumed by Canvas.drawVertices. Covers builder construction, per-mode triangle counting, bounds computation, and the convenience sk_vertices_triangles factory.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-VERT |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/vertices_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkVertices and SkVerticesBuilder — Skia's immutable triangle-mesh
primitive consumed by Canvas.drawVertices. Covers builder construction,
per-mode triangle counting, bounds computation, and the convenience
sk_vertices_triangles factory.

## Scenarios

### SkVertices

#### builder: new has zero vertices and Triangles mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = sk_vertices_builder_new()
expect(b.positions.len()).to_equal(0)
expect(b.texcoords.len()).to_equal(0)
expect(b.colors.len()).to_equal(0)
expect(b.indices.len()).to_equal(0)
val is_triangles = b.mode == VertexMode.Triangles
expect(is_triangles).to_equal(true)
```

</details>

#### builder: add_vertex appends positions

1. var b = sk vertices builder new
2. b add vertex
3. b add vertex
4. b add vertex
   - Expected: b.positions.len() equals `3`
   - Expected: b.positions[0].x equals `1.0`
   - Expected: b.positions[1].y equals `4.0`
   - Expected: b.positions[2].x equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = sk_vertices_builder_new()
b.add_vertex(1.0, 2.0)
b.add_vertex(3.0, 4.0)
b.add_vertex(5.0, 6.0)
expect(b.positions.len()).to_equal(3)
expect(b.positions[0].x).to_equal(1.0)
expect(b.positions[1].y).to_equal(4.0)
expect(b.positions[2].x).to_equal(5.0)
```

</details>

#### builder: build() produces SkVertices with computed bounds

1. var b = sk vertices builder new
2. b add vertex
3. b add vertex
4. b add vertex
   - Expected: v.positions.len() equals `3`
   - Expected: v.bounds.left equals `0.0`
   - Expected: v.bounds.top equals `0.0`
   - Expected: v.bounds.right equals `10.0`
   - Expected: v.bounds.bottom equals `8.0`
   - Expected: v.is_indexed() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = sk_vertices_builder_new()
b.add_vertex(0.0, 0.0)
b.add_vertex(10.0, 0.0)
b.add_vertex(5.0, 8.0)
val v = b.build()
expect(v.positions.len()).to_equal(3)
expect(v.bounds.left).to_equal(0.0)
expect(v.bounds.top).to_equal(0.0)
expect(v.bounds.right).to_equal(10.0)
expect(v.bounds.bottom).to_equal(8.0)
expect(v.is_indexed()).to_equal(false)
```

</details>

#### SkVertices: triangle_count for 6 triangle-list vertices is 2

1. var b = sk vertices builder new
2. b set mode
3. b add vertex
4. b add vertex
5. b add vertex
6. b add vertex
7. b add vertex
8. b add vertex
   - Expected: v.triangle_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = sk_vertices_builder_new()
b.set_mode(VertexMode.Triangles)
b.add_vertex(0.0, 0.0)
b.add_vertex(1.0, 0.0)
b.add_vertex(0.0, 1.0)
b.add_vertex(2.0, 0.0)
b.add_vertex(3.0, 0.0)
b.add_vertex(2.0, 1.0)
val v = b.build()
expect(v.triangle_count()).to_equal(2)
```

</details>

#### SkVertices: triangle_count for 5 triangle-strip vertices is 3

1. var b = sk vertices builder new
2. b set mode
3. b add vertex
4. b add vertex
5. b add vertex
6. b add vertex
7. b add vertex
   - Expected: v.triangle_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var b = sk_vertices_builder_new()
b.set_mode(VertexMode.TriangleStrip)
b.add_vertex(0.0, 0.0)
b.add_vertex(1.0, 0.0)
b.add_vertex(0.0, 1.0)
b.add_vertex(1.0, 1.0)
b.add_vertex(2.0, 1.0)
val v = b.build()
expect(v.triangle_count()).to_equal(3)
```

</details>

#### sk_vertices_triangles: empty inputs produce empty vertices with zero triangle count

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_pts: [SkPoint] = []
val empty_colors: [SkColor4f] = []
val empty_uvs: [SkPoint] = []
val v = sk_vertices_triangles(empty_pts, empty_colors, empty_uvs)
expect(v.positions.len()).to_equal(0)
expect(v.colors.len()).to_equal(0)
expect(v.texcoords.len()).to_equal(0)
expect(v.triangle_count()).to_equal(0)
expect(v.is_indexed()).to_equal(false)
expect(v.bounds.left).to_equal(0.0)
expect(v.bounds.right).to_equal(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
