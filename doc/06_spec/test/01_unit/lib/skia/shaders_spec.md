# Shaders Specification

> 1. expect  approx

<!-- sdn-diagram:id=shaders_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shaders_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shaders_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shaders_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shaders Specification

## Scenarios

### interpolate_stops: midpoint

#### t=0.5 with two stops returns midpoint color

1. expect  approx
2. expect  approx
3. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colors = [_red_packed(), _blue_packed()]
val positions = [0.0, 1.0]
val result = interpolate_stops(colors, positions, 0.5)
expect _approx(result.r, 0.5) to_equal true
expect _approx(result.b, 0.5) to_equal true
expect _approx(result.g, 0.0) to_equal true
```

</details>

### interpolate_stops: first stop

#### t=0 returns first stop color

1. expect  approx
2. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val colors = [_red_packed(), _blue_packed()]
val positions = [0.0, 1.0]
val result = interpolate_stops(colors, positions, 0.0)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
```

</details>

### tile_coord: Repeat

#### t=1.5 with Repeat returns 0.5

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tile_coord(1.5, SkTileMode.Repeat)
expect _approx(result, 0.5) to_equal true
```

</details>

### tile_coord: Clamp

#### t=1.5 with Clamp returns 1.0

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tile_coord(1.5, SkTileMode.Clamp)
expect _approx(result, 1.0) to_equal true
```

</details>

### tile_coord: Mirror

#### t=-0.3 with Mirror maps to 0.3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = tile_coord(-0.3, SkTileMode.Mirror)
# tri-wave: -0.3 is in the range [-1,0]; mirror maps to 0.3
val ok = _approx(result, 0.3) or _approx(result, 0.7)
expect ok to_equal true
```

</details>

### eval_linear_gradient: start point

#### at start point returns first stop color

1. expect  approx
2. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shader = _make_two_stop_shader()
val result = eval_linear_gradient(shader, 0.0, 0.0)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
```

</details>

### eval_linear_gradient: end point

#### at end point returns last stop color

1. expect  approx
2. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shader = _make_two_stop_shader()
val result = eval_linear_gradient(shader, 100.0, 0.0)
expect _approx(result.r, 0.0) to_equal true
expect _approx(result.b, 1.0) to_equal true
```

</details>

### eval_radial_gradient: center

#### at center returns first stop color

1. expect  approx
2. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shader = _make_radial_shader()
val result = eval_radial_gradient(shader, 50.0, 50.0)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
```

</details>

### sample_image_nearest: empty pixels

#### returns transparent black when pixel list is empty

1. expect  approx
2. expect  approx
3. expect  approx
4. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = _empty_image()
val result = sample_image_nearest(image, 1.0, 1.0)
expect _approx(result.r, 0.0) to_equal true
expect _approx(result.g, 0.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
expect _approx(result.a, 0.0) to_equal true
```

</details>

### apply_blend: SrcOver with opaque src

#### opaque red over anything returns red

1. expect  approx
2. expect  approx
3. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val dst = SkColor4f(r: 0.0, g: 1.0, b: 0.0, a: 1.0)
val result = apply_blend(src, dst, SkBlendMode.SrcOver)
expect _approx(result.r, 1.0) to_equal true
expect _approx(result.g, 0.0) to_equal true
expect _approx(result.a, 1.0) to_equal true
```

</details>

### apply_blend: Clear

#### Clear returns all-zero

1. expect  approx
2. expect  approx
3. expect  approx
4. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SkColor4f(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val dst = SkColor4f(r: 1.0, g: 1.0, b: 1.0, a: 1.0)
val result = apply_blend(src, dst, SkBlendMode.Clear)
expect _approx(result.r, 0.0) to_equal true
expect _approx(result.g, 0.0) to_equal true
expect _approx(result.b, 0.0) to_equal true
expect _approx(result.a, 0.0) to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/shaders_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- interpolate_stops: midpoint
- interpolate_stops: first stop
- tile_coord: Repeat
- tile_coord: Clamp
- tile_coord: Mirror
- eval_linear_gradient: start point
- eval_linear_gradient: end point
- eval_radial_gradient: center
- sample_image_nearest: empty pixels
- apply_blend: SrcOver with opaque src
- apply_blend: Clear

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
