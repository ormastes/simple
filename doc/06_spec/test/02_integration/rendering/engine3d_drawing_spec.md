# Engine3d Drawing Specification

> 1. var engine = Engine3D create with backend

<!-- sdn-diagram:id=engine3d_drawing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine3d_drawing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine3d_drawing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine3d_drawing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine3d Drawing Specification

## Scenarios

### Engine3D Drawing

#### cpu backend

#### clear fills framebuffer with color

1. var engine = Engine3D create with backend
2. engine begin frame
3. engine clear
4. engine end frame
   - Expected: color3d_r(p) equals `255`
   - Expected: color3d_g(p) equals `0`
   - Expected: color3d_b(p) equals `0`
   - Expected: color3d_r(p2) equals `255`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create_with_backend(8, 8, "cpu")
engine.begin_frame()
engine.clear(0xFFFF0000)
engine.end_frame()
val pixels = engine.read_pixels()
val p = pixels[0]
expect(color3d_r(p)).to_equal(255)
expect(color3d_g(p)).to_equal(0)
expect(color3d_b(p)).to_equal(0)
val p2 = pixels[63]
expect(color3d_r(p2)).to_equal(255)
engine.shutdown()
```

</details>

#### clear_depth resets depth buffer

1. var engine = Engine3D create with backend
2. engine begin frame
3. engine clear depth
4. engine end frame
   - Expected: (depth[0] as i32) equals `1`
   - Expected: (depth[15] as i32) equals `1`
5. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create_with_backend(4, 4, "cpu")
engine.begin_frame()
engine.clear_depth()
engine.end_frame()
val depth = engine.read_depth()
expect((depth[0] as i32)).to_equal(1)
expect((depth[15] as i32)).to_equal(1)
engine.shutdown()
```

</details>

#### submit_triangle renders a triangle

1. var engine = Engine3D create with backend
2. engine begin frame
3. engine clear
4. engine clear depth
5. engine set depth test
6. engine set cull mode
7. engine set camera
8. engine submit triangle
9. engine end frame
   - Expected: color3d_r(center) equals `255`
   - Expected: color3d_g(center) equals `0`
10. engine shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var engine = Engine3D.create_with_backend(10, 10, "cpu")
engine.begin_frame()
engine.clear(0xFF000000)
engine.clear_depth()
engine.set_depth_test(false)
engine.set_cull_mode(0)
val view = mat4_look_at(0.0, 0.0, 5.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0)
val proj = mat4_perspective(1.0, 1.0, 0.1, 100.0)
engine.set_camera(view, proj)
val v0 = vertex3d_pos_color(0.0, 1.0, 0.0, 0xFFFF0000)
val v1 = vertex3d_pos_color(-1.0, -1.0, 0.0, 0xFFFF0000)
val v2 = vertex3d_pos_color(1.0, -1.0, 0.0, 0xFFFF0000)
val mat = material_unlit(0xFFFF0000)
val model = mat4_identity()
engine.submit_triangle(v0, v1, v2, mat, model)
engine.end_frame()
val pixels = engine.read_pixels()
# Center pixel (5,5) should be red (inside triangle)
val center = pixels[5 * 10 + 5]
expect(color3d_r(center)).to_equal(255)
expect(color3d_g(center)).to_equal(0)
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/engine3d_drawing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D Drawing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
