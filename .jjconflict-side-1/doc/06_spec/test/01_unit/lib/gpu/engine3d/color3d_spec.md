# Color3d Specification

> <details>

<!-- sdn-diagram:id=color3d_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color3d_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color3d_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color3d_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Color3d Specification

## Scenarios

### Engine3D Color3D

#### rgba3d packing

#### packs red channel correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(255, 0, 0, 255)
expect(c3d_r(c)).to_equal(255)
```

</details>

#### packs green channel correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(0, 128, 0, 255)
expect(c3d_g(c)).to_equal(128)
```

</details>

#### packs blue channel correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(0, 0, 64, 255)
expect(c3d_b(c)).to_equal(64)
```

</details>

#### packs alpha channel correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(0, 0, 0, 200)
expect(c3d_a(c)).to_equal(200)
```

</details>

#### rgb3d packing

#### packs with alpha 255

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb3d(100, 150, 200)
expect(c3d_a(c)).to_equal(255)
```

</details>

#### packs red channel

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgb3d(100, 150, 200)
expect(c3d_r(c)).to_equal(100)
```

</details>

#### channel extraction

#### c3d_r extracts red

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(255, 128, 64, 200)
expect(c3d_r(c)).to_equal(255)
```

</details>

#### c3d_g extracts green

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(255, 128, 64, 200)
expect(c3d_g(c)).to_equal(128)
```

</details>

#### c3d_b extracts blue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(255, 128, 64, 200)
expect(c3d_b(c)).to_equal(64)
```

</details>

#### c3d_a extracts alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = rgba3d(255, 128, 64, 200)
expect(c3d_a(c)).to_equal(200)
```

</details>

#### luminance3d

#### white returns approximately 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lum = luminance3d(rgba3d(255, 255, 255, 255))
expect((lum as i32)).to_equal(1)
```

</details>

#### black returns 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lum = luminance3d(rgba3d(0, 0, 0, 255))
expect((lum as i32)).to_equal(0)
```

</details>

#### blend3d

#### blending with alpha=0 returns base unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = rgba3d(100, 150, 200, 255)
val overlay = rgba3d(0, 0, 0, 0)
val result = blend3d(overlay, base)
expect(c3d_r(result)).to_equal(c3d_r(base))
expect(c3d_g(result)).to_equal(c3d_g(base))
expect(c3d_b(result)).to_equal(c3d_b(base))
```

</details>

#### blending with alpha=255 returns src

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = rgba3d(0, 0, 0, 255)
val overlay = rgba3d(200, 100, 50, 255)
val result = blend3d(overlay, base)
expect(c3d_r(result)).to_equal(200)
```

</details>

#### lerp_color3d

#### t=0 returns first color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rgba3d(255, 0, 0, 255)
val b = rgba3d(0, 255, 0, 255)
val result = lerp_color3d(a, b, 0.0)
expect(c3d_r(result)).to_equal(255)
expect(c3d_g(result)).to_equal(0)
```

</details>

#### t=1 returns second color

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = rgba3d(255, 0, 0, 255)
val b = rgba3d(0, 255, 0, 255)
val result = lerp_color3d(a, b, 1.0)
expect(c3d_r(result)).to_equal(0)
expect(c3d_g(result)).to_equal(255)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine3d/color3d_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Engine3D Color3D

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
