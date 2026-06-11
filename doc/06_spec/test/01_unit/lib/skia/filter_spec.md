# Filter Specification

> 1. expect  approx

<!-- sdn-diagram:id=filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

filter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Filter Specification

## Scenarios

### Gaussian kernel

#### sums to approximately 1.0 for sigma=1.0

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = gaussian_kernel(1.0)
val s = _sum_kernel(k)
expect _approx(s, 1.0) to_equal true
```

</details>

#### sums to approximately 1.0 for sigma=2.0

1. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = gaussian_kernel(2.0)
val s = _sum_kernel(k)
expect _approx(s, 1.0) to_equal true
```

</details>

#### returns single element [1.0] for sigma=0.0

1. expect k len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = gaussian_kernel(0.0)
expect k.len() to_equal 1
```

</details>

#### kernel is symmetric for sigma=1.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = gaussian_kernel(1.5)
val n = k.len().to_i32()
var ok = true
var i = 0
while i < n / 2:
    val diff = k[i.to_i64()] - k[(n - 1 - i).to_i64()]
    val ad = if diff < 0.0: -diff else: diff
    if ad > 0.000001:
        ok = false
    i = i + 1
expect ok to_equal true
```

</details>

### Horizontal blur

#### spreads color to neighbors from single white pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _white_center_5x5()
val blurred = blur_horizontal(buf, 1.0)
val center = blurred.pixels[12]
val neighbor = blurred.pixels[11]
expect center.r < 1.0 to_equal true
expect neighbor.r > 0.0 to_equal true
```

</details>

#### preserves buffer dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _white_center_5x5()
val blurred = blur_horizontal(buf, 1.0)
expect blurred.width to_equal 5
expect blurred.height to_equal 5
```

</details>

### Color matrix filter

<details>
<summary>Advanced: identity matrix returns input unchanged</summary>

#### identity matrix returns input unchanged

1. expect  approx
2. expect  approx
3. expect  approx
4. expect  approx


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = SkColor4f(r: 0.4, g: 0.6, b: 0.2, a: 1.0)
val buf = ImageBuffer(width: 1, height: 1, pixels: [src])
val result = apply_color_matrix(buf, _identity_matrix())
expect _approx(result.pixels[0].r, 0.4) to_equal true
expect _approx(result.pixels[0].g, 0.6) to_equal true
expect _approx(result.pixels[0].b, 0.2) to_equal true
expect _approx(result.pixels[0].a, 1.0) to_equal true
```

</details>


</details>

<details>
<summary>Advanced: clamps results to 1.0 when matrix doubles channels</summary>

#### clamps results to 1.0 when matrix doubles channels

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = [2.0, 0.0, 0.0, 0.0, 0.0,
              0.0, 2.0, 0.0, 0.0, 0.0,
              0.0, 0.0, 2.0, 0.0, 0.0,
              0.0, 0.0, 0.0, 2.0, 0.0]
val src = SkColor4f(r: 0.8, g: 0.8, b: 0.8, a: 0.8)
val buf = ImageBuffer(width: 1, height: 1, pixels: [src])
val result = apply_color_matrix(buf, matrix)
expect result.pixels[0].r to_equal 1.0
```

</details>


</details>

<details>
<summary>Advanced: clamps results to 0.0 when matrix negates channels</summary>

#### clamps results to 0.0 when matrix negates channels

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = [-1.0, 0.0, 0.0, 0.0, 0.0,
               0.0, -1.0, 0.0, 0.0, 0.0,
               0.0, 0.0, -1.0, 0.0, 0.0,
               0.0, 0.0, 0.0, 1.0, 0.0]
val src = SkColor4f(r: 0.5, g: 0.5, b: 0.5, a: 1.0)
val buf = ImageBuffer(width: 1, height: 1, pixels: [src])
val result = apply_color_matrix(buf, matrix)
expect result.pixels[0].r to_equal 0.0
```

</details>


</details>

### Drop shadow

#### result has same dimensions as source

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _white_center_5x5()
val shadow_color = SkColor4f(r: 0.0, g: 0.0, b: 0.0, a: 1.0)
val result = drop_shadow(src, 1.0, 1.0, 0.5, 0.5, shadow_color)
expect result.width to_equal 5
expect result.height to_equal 5
```

</details>

#### result pixel count matches source

1. expect result pixels len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = _white_center_5x5()
val shadow_color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val result = drop_shadow(src, 1.0, 1.0, 0.3, 0.3, shadow_color)
expect result.pixels.len() to_equal 25
```

</details>

### Gaussian blur end-to-end

#### two-pass blur spreads energy from single white pixel

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = _white_center_5x5()
val result = gaussian_blur(buf, 1.0, 1.0)
val center = result.pixels[12]
val corner = result.pixels[0]
expect center.r < 1.0 to_equal true
expect corner.r > 0.0 to_equal true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Gaussian kernel
- Horizontal blur
- Color matrix filter
- Drop shadow
- Gaussian blur end-to-end

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
