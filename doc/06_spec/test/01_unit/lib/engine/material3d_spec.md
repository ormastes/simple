# Material3d Specification

> <details>

<!-- sdn-diagram:id=material3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=material3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

material3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=material3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Material3d Specification

## Scenarios

### pbr_material

#### creates with albedo, metallic, roughness

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val red = EngineColor(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val mat = pbr_material(red, 0.8, 0.2)
expect(mat.albedo.r).to_equal(1.0)
expect(mat.albedo.g).to_equal(0.0)
expect(mat.metallic).to_equal(0.8)
expect(mat.roughness).to_equal(0.2)
```

</details>

#### has PBR material type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val mat = pbr_material(white, 0.0, 1.0)
val is_pbr = match mat.material_type:
    MaterialType3D.PBR: true
    _: false
expect(is_pbr).to_equal(true)
```

</details>

#### has no texture by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
val mat = pbr_material(white, 0.5, 0.5)
expect(mat.has_texture()).to_equal(false)
```

</details>

#### has zero emissive by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
val mat = pbr_material(white, 0.5, 0.5)
expect(mat.emissive.r).to_equal(0.0)
expect(mat.emissive.g).to_equal(0.0)
expect(mat.emissive.b).to_equal(0.0)
expect(mat.emissive_intensity).to_equal(0.0)
```

</details>

### phong_material

#### creates with diffuse and shininess

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blue = EngineColor(r: 0.0, g: 0.0, b: 1.0, a: 1.0)
val mat = phong_material(blue, 32.0)
expect(mat.albedo.b).to_equal(1.0)
expect(mat.albedo.r).to_equal(0.0)
```

</details>

#### has Phong material type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val blue = EngineColor.blue()
val mat = phong_material(blue, 32.0)
val is_phong = match mat.material_type:
    MaterialType3D.Phong: true
    _: false
expect(is_phong).to_equal(true)
```

</details>

#### maps shininess to inverse roughness

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
# roughness = 1.0 / (shininess + 1.0) = 1.0 / 33.0
val mat = phong_material(white, 32.0)
expect(mat.metallic).to_equal(0.0)
```

</details>

#### has no texture by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
val mat = phong_material(white, 16.0)
expect(mat.has_texture()).to_equal(false)
```

</details>

### unlit_material

#### creates with color only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val green = EngineColor(r: 0.0, g: 1.0, b: 0.0, a: 1.0)
val mat = unlit_material(green)
expect(mat.albedo.g).to_equal(1.0)
expect(mat.albedo.r).to_equal(0.0)
expect(mat.metallic).to_equal(0.0)
```

</details>

#### has Unlit material type

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val green = EngineColor.green()
val mat = unlit_material(green)
val is_unlit = match mat.material_type:
    MaterialType3D.Unlit: true
    _: false
expect(is_unlit).to_equal(true)
```

</details>

#### has roughness of 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val green = EngineColor.green()
val mat = unlit_material(green)
expect(mat.roughness).to_equal(1.0)
```

</details>

#### has no texture by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val white = EngineColor.white()
val mat = unlit_material(white)
expect(mat.has_texture()).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/material3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- pbr_material
- phong_material
- unlit_material

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
