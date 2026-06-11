# Types3d Specification

> <details>

<!-- sdn-diagram:id=types3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=types3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

types3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=types3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Types3d Specification

## Scenarios

### Engine3D Types

#### vertex constructors

#### vertex3d_pos sets position and defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vertex3d_pos(1.0, 2.0, 3.0)
expect((v.px as i32)).to_equal(1)
expect((v.py as i32)).to_equal(2)
expect((v.pz as i32)).to_equal(3)
expect(v.color).to_equal(0xFFFFFFFF)
```

</details>

#### vertex3d_pos_color sets position and color

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vertex3d_pos_color(0.0, 0.0, 0.0, 0xFFFF0000)
expect(v.color).to_equal(0xFFFF0000)
```

</details>

#### material constructors

#### material_unlit has kind 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = material_unlit(0xFFFF0000)
expect(m.kind).to_equal(MATERIAL_UNLIT)
expect(m.albedo).to_equal(0xFFFF0000)
expect(m.texture_id).to_equal(-1)
```

</details>

#### material_phong has kind 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = material_phong(0xFFFFFFFF, 0xFF888888, 32.0)
expect(m.kind).to_equal(MATERIAL_PHONG)
expect((m.shininess as i32)).to_equal(32)
```

</details>

#### material_pbr has kind 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = material_pbr(0xFFCCCCCC, 0.5, 0.3)
expect(m.kind).to_equal(MATERIAL_PBR)
```

</details>

#### light constructors

#### light_directional has kind 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = light_directional(0.0, -1.0, 0.0, 0xFFFFFFFF, 1.0)
expect(l.kind).to_equal(LIGHT_DIRECTIONAL)
expect((l.dy as i32)).to_equal(-1)
```

</details>

#### light_point has kind 1 and range

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = light_point(5.0, 5.0, 5.0, 0xFFFFFFFF, 1.0, 10.0)
expect(l.kind).to_equal(LIGHT_POINT)
expect((l.range as i32)).to_equal(10)
```

</details>

#### color helpers

#### pack and unpack ARGB

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = color3d_pack(255, 128, 64, 200)
expect(color3d_r(c)).to_equal(255)
expect(color3d_g(c)).to_equal(128)
expect(color3d_b(c)).to_equal(64)
expect(color3d_a(c)).to_equal(200)
```

</details>

#### pack_rgb sets alpha to 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = color3d_pack_rgb(100, 150, 200)
expect(color3d_a(c)).to_equal(255)
expect(color3d_r(c)).to_equal(100)
```

</details>

#### mat4 math

#### identity transform preserves point

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = mat4_identity()
val p = mat4_transform_point(id, 3.0, 4.0, 5.0)
expect((p[0] as i32)).to_equal(3)
expect((p[1] as i32)).to_equal(4)
expect((p[2] as i32)).to_equal(5)
```

</details>

#### translate shifts point

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = mat4_translate(10.0, 20.0, 30.0)
val p = mat4_transform_point(t, 1.0, 2.0, 3.0)
expect((p[0] as i32)).to_equal(11)
expect((p[1] as i32)).to_equal(22)
expect((p[2] as i32)).to_equal(33)
```

</details>

#### scale multiplies components

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = mat4_scale(2.0, 3.0, 4.0)
val p = mat4_transform_point(s, 1.0, 1.0, 1.0)
expect((p[0] as i32)).to_equal(2)
expect((p[1] as i32)).to_equal(3)
expect((p[2] as i32)).to_equal(4)
```

</details>

#### mul identity is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = mat4_identity()
val t = mat4_translate(5.0, 6.0, 7.0)
val r = mat4_mul(id, t)
val p = mat4_transform_point(r, 0.0, 0.0, 0.0)
expect((p[0] as i32)).to_equal(5)
expect((p[1] as i32)).to_equal(6)
```

</details>

#### vec3 math

#### dot product

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = vec3_dot(1.0, 0.0, 0.0, 0.0, 1.0, 0.0)
expect((d as i32)).to_equal(0)
val d2 = vec3_dot(1.0, 0.0, 0.0, 1.0, 0.0, 0.0)
expect((d2 as i32)).to_equal(1)
```

</details>

#### length of unit vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val l = vec3_length(1.0, 0.0, 0.0)
expect((l as i32)).to_equal(1)
```

</details>

#### normalize

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = vec3_normalize(3.0, 0.0, 0.0)
expect((n[0] as i32)).to_equal(1)
expect((n[1] as i32)).to_equal(0)
expect((n[2] as i32)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/types3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D Types

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
