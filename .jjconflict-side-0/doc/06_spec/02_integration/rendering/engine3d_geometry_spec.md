# Engine3d Geometry Specification

> 1. var engine = Engine3D create with backend

<!-- sdn-diagram:id=engine3d_geometry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine3d_geometry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine3d_geometry_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine3d_geometry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine3d Geometry Specification

## Scenarios

### Engine3D Geometry Primitives

#### cpu backend

#### draw_cube renders pixels

1. var engine = Engine3D create with backend
2. engine begin frame
3. engine clear
4. engine clear depth
5. engine set cull mode
6. engine set camera
7. engine draw cube
8. engine end frame
   - Expected: color3d_g(center) equals `255`
9. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create_with_backend(16, 16, "cpu")
engine.begin_frame()
engine.clear(0xFF000000)
engine.clear_depth()
engine.set_cull_mode(0)
val view = mat4_look_at(0.0, 0.0, 3.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
val proj = mat4_perspective(1.0, 1.0, 0.1, 100.0)
engine.set_camera(view, proj)
val mat = material_unlit(0xFF00FF00)
engine.draw_cube(mat4_identity(), mat)
engine.end_frame()
val pixels = engine.read_pixels()
val center = pixels[8 * 16 + 8]
expect(color3d_g(center)).to_equal(255)
engine.shutdown()
```

</details>

#### draw_plane renders pixels

1. var engine = Engine3D create with backend
2. engine begin frame
3. engine clear
4. engine clear depth
5. engine set cull mode
6. engine set camera
7. engine draw plane
8. engine end frame
9. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create_with_backend(16, 16, "cpu")
engine.begin_frame()
engine.clear(0xFF000000)
engine.clear_depth()
engine.set_cull_mode(0)
val view = mat4_look_at(0.0, 2.0, 2.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
val proj = mat4_perspective(1.0, 1.0, 0.1, 100.0)
engine.set_camera(view, proj)
val mat = material_unlit(0xFF0000FF)
engine.draw_plane(mat4_identity(), mat)
engine.end_frame()
val pixels = engine.read_pixels()
# At least some pixels should be blue
var blue_count = 0
var i = 0
while i < 256:
    if color3d_b(pixels[i]) > 200:
        blue_count = blue_count + 1
    i = i + 1
expect(blue_count).to_be_greater_than(0)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine3d_geometry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D Geometry Primitives

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
