# Texture3d Specification

> <details>

<!-- sdn-diagram:id=texture3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=texture3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

texture3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=texture3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Texture3d Specification

## Scenarios

### Engine3D Textures

#### TextureDescriptor3D.create_2d

#### sets width and height

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_2d(256, 128, TEX_FMT_RGBA8_UNORM)
expect(t.width).to_equal(256)
expect(t.height).to_equal(128)
```

</details>

#### dimension is TEX_DIM_2D

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_2d(64, 64, TEX_FMT_RGBA8_UNORM)
expect(t.dimension).to_equal(TEX_DIM_2D)
```

</details>

#### depth_or_layers is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_2d(64, 64, TEX_FMT_RGBA8_UNORM)
expect(t.depth_or_layers).to_equal(1)
```

</details>

#### TextureDescriptor3D.create_3d

#### dimension is TEX_DIM_3D

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_3d(32, 32, 16, TEX_FMT_RGBA8_UNORM)
expect(t.dimension).to_equal(TEX_DIM_3D)
```

</details>

#### depth_or_layers matches depth argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_3d(32, 32, 16, TEX_FMT_RGBA8_UNORM)
expect(t.depth_or_layers).to_equal(16)
```

</details>

#### TextureDescriptor3D.create_cube

#### dimension is TEX_DIM_CUBE

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_cube(128, TEX_FMT_RGBA8_UNORM)
expect(t.dimension).to_equal(TEX_DIM_CUBE)
```

</details>

#### depth_or_layers is 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_cube(128, TEX_FMT_RGBA8_UNORM)
expect(t.depth_or_layers).to_equal(6)
```

</details>

#### TextureDescriptor3D.create_depth

#### format is TEX_FMT_DEPTH32_FLOAT

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_depth(1920, 1080)
expect(t.format).to_equal(TEX_FMT_DEPTH32_FLOAT)
```

</details>

#### dimension is TEX_DIM_2D

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_depth(1920, 1080)
expect(t.dimension).to_equal(TEX_DIM_2D)
```

</details>

#### TextureDescriptor3D.create_2d_array

#### dimension is TEX_DIM_2D_ARRAY

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_2d_array(256, 256, 4, TEX_FMT_RGBA8_UNORM)
expect(t.dimension).to_equal(TEX_DIM_2D_ARRAY)
```

</details>

#### depth_or_layers matches layers argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = TextureDescriptor3D.create_2d_array(256, 256, 8, TEX_FMT_RGBA8_UNORM)
expect(t.depth_or_layers).to_equal(8)
```

</details>

#### SamplerDescriptor3D.create_default

#### mag_filter is FILTER_LINEAR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SamplerDescriptor3D.create_default()
expect(s.mag_filter).to_equal(FILTER_LINEAR)
```

</details>

#### min_filter is FILTER_LINEAR

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SamplerDescriptor3D.create_default()
expect(s.min_filter).to_equal(FILTER_LINEAR)
```

</details>

#### SamplerDescriptor3D.create_nearest

#### mag_filter is FILTER_NEAREST

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SamplerDescriptor3D.create_nearest()
expect(s.mag_filter).to_equal(FILTER_NEAREST)
```

</details>

#### min_filter is FILTER_NEAREST

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SamplerDescriptor3D.create_nearest()
expect(s.min_filter).to_equal(FILTER_NEAREST)
```

</details>

#### SamplerDescriptor3D.create_shadow

#### compare is COMPARE_LESS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = SamplerDescriptor3D.create_shadow()
expect(s.compare).to_equal(COMPARE_LESS)
```

</details>

#### bytes_per_pixel_3d

#### RGBA8 returns 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_per_pixel_3d(TEX_FMT_RGBA8_UNORM)).to_equal(4)
```

</details>

#### DEPTH32_FLOAT returns 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(bytes_per_pixel_3d(TEX_FMT_DEPTH32_FLOAT)).to_equal(4)
```

</details>

#### is_depth_format

#### DEPTH32_FLOAT is depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_depth_format(TEX_FMT_DEPTH32_FLOAT)).to_equal(true)
```

</details>

#### RGBA8_UNORM is not depth

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_depth_format(TEX_FMT_RGBA8_UNORM)).to_equal(false)
```

</details>

#### is_compressed_format

#### BC1_UNORM is compressed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed_format(TEX_FMT_BC1_UNORM)).to_equal(true)
```

</details>

#### RGBA8_UNORM is not compressed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_compressed_format(TEX_FMT_RGBA8_UNORM)).to_equal(false)
```

</details>

#### TEX_DIM constants

#### TEX_DIM_2D is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TEX_DIM_2D).to_equal(0)
```

</details>

#### TEX_DIM_3D is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TEX_DIM_3D).to_equal(1)
```

</details>

#### TEX_DIM_CUBE is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(TEX_DIM_CUBE).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/texture3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D Textures

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
