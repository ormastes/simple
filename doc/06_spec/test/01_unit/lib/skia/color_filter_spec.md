# Skia Color Filter Specification

> Tests for per-pixel color filters mirroring Skia's SkColorFilters: Identity, Invert, Grayscale, Matrix4x5, Lerp, and BlendMode passthrough. Covers both scalar (apply_color_filter_to_pixel) and bitmap (apply_color_filter_to_bitmap) dispatch paths.

<!-- sdn-diagram:id=color_filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_filter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Color Filter Specification

Tests for per-pixel color filters mirroring Skia's SkColorFilters: Identity, Invert, Grayscale, Matrix4x5, Lerp, and BlendMode passthrough. Covers both scalar (apply_color_filter_to_pixel) and bitmap (apply_color_filter_to_bitmap) dispatch paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-COLORFILTER |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/color_filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for per-pixel color filters mirroring Skia's SkColorFilters: Identity,
Invert, Grayscale, Matrix4x5, Lerp, and BlendMode passthrough. Covers both
scalar (apply_color_filter_to_pixel) and bitmap (apply_color_filter_to_bitmap)
dispatch paths.

## Scenarios

### color_filter

#### apply_color_filter_to_pixel: Identity returns input unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = color_filter_identity()
val out = apply_color_filter_to_pixel(0.25, 0.5, 0.75, 0.8, f)
val r_ok = math_abs(out.0 - 0.25) < 1e-9
val g_ok = math_abs(out.1 - 0.5) < 1e-9
val b_ok = math_abs(out.2 - 0.75) < 1e-9
val a_ok = math_abs(out.3 - 0.8) < 1e-9
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

#### apply_color_filter_to_pixel: Invert turns (1,0,0,1) into (0,1,1,1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = color_filter_invert()
val out = apply_color_filter_to_pixel(1.0, 0.0, 0.0, 1.0, f)
val r_ok = math_abs(out.0 - 0.0) < 1e-9
val g_ok = math_abs(out.1 - 1.0) < 1e-9
val b_ok = math_abs(out.2 - 1.0) < 1e-9
val a_ok = math_abs(out.3 - 1.0) < 1e-9
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

#### apply_color_filter_to_pixel: Grayscale of pure red gives l ~ 0.299

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = color_filter_grayscale()
val out = apply_color_filter_to_pixel(1.0, 0.0, 0.0, 1.0, f)
val l = out.0
val l_close = math_abs(l - 0.299) < 1e-9
expect(l_close).to_equal(true)
# R == G == B for grayscale output
val gb_match = math_abs(out.1 - l) < 1e-12 and math_abs(out.2 - l) < 1e-12
expect(gb_match).to_equal(true)
expect(l).to_be_greater_than(0.0)
expect(l).to_be_less_than(1.0)
```

</details>

<details>
<summary>Advanced: apply_color_filter_to_pixel: Matrix with identity matrix returns input unchanged</summary>

#### apply_color_filter_to_pixel: Matrix with identity matrix returns input unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id_m = [1.0, 0.0, 0.0, 0.0, 0.0,
            0.0, 1.0, 0.0, 0.0, 0.0,
            0.0, 0.0, 1.0, 0.0, 0.0,
            0.0, 0.0, 0.0, 1.0, 0.0]
val f = color_filter_matrix(id_m)
val out = apply_color_filter_to_pixel(0.2, 0.4, 0.6, 0.9, f)
val r_ok = math_abs(out.0 - 0.2) < 1e-9
val g_ok = math_abs(out.1 - 0.4) < 1e-9
val b_ok = math_abs(out.2 - 0.6) < 1e-9
val a_ok = math_abs(out.3 - 0.9) < 1e-9
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>


</details>

#### apply_color_filter_to_pixel: Grayscale preserves alpha

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = color_filter_grayscale()
val alpha_in = 0.42
val out = apply_color_filter_to_pixel(0.8, 0.3, 0.1, alpha_in, f)
val a_ok = math_abs(out.3 - alpha_in) < 1e-12
expect(a_ok).to_equal(true)
```

</details>

#### apply_color_filter_to_bitmap: Invert on a 2x2 bitmap returns inverted pixels

1. bmp set pixel
2. bmp set pixel
3. bmp set pixel
4. bmp set pixel
   - Expected: out.width equals `2`
   - Expected: out.height equals `2`
   - Expected: out.pixels[0] equals `0 as u8`
   - Expected: out.pixels[1] equals `255 as u8`
   - Expected: out.pixels[2] equals `255 as u8`
   - Expected: out.pixels[3] equals `255 as u8`
   - Expected: out.pixels[4] equals `255 as u8`
   - Expected: out.pixels[5] equals `0 as u8`
   - Expected: out.pixels[6] equals `255 as u8`
   - Expected: out.pixels[7] equals `255 as u8`
   - Expected: out.pixels[8] equals `255 as u8`
   - Expected: out.pixels[9] equals `255 as u8`
   - Expected: out.pixels[10] equals `0 as u8`
   - Expected: out.pixels[11] equals `255 as u8`
   - Expected: out.pixels[12] equals `0 as u8`
   - Expected: out.pixels[13] equals `0 as u8`
   - Expected: out.pixels[14] equals `0 as u8`
   - Expected: out.pixels[15] equals `255 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bmp = Bitmap.zeros(2, 2)
# pixel (0,0) = red, fully opaque
bmp.set_pixel(0, 0, sk_color4f(1.0, 0.0, 0.0, 1.0))
# pixel (1,0) = green, fully opaque
bmp.set_pixel(1, 0, sk_color4f(0.0, 1.0, 0.0, 1.0))
# pixel (0,1) = blue, fully opaque
bmp.set_pixel(0, 1, sk_color4f(0.0, 0.0, 1.0, 1.0))
# pixel (1,1) = white, fully opaque
bmp.set_pixel(1, 1, sk_color4f(1.0, 1.0, 1.0, 1.0))
val f = color_filter_invert()
val out = apply_color_filter_to_bitmap(bmp, f)
expect(out.width).to_equal(2)
expect(out.height).to_equal(2)
# Red (255,0,0,255) -> (0,255,255,255)
expect(out.pixels[0]).to_equal(0 as u8)
expect(out.pixels[1]).to_equal(255 as u8)
expect(out.pixels[2]).to_equal(255 as u8)
expect(out.pixels[3]).to_equal(255 as u8)
# Green (0,255,0,255) -> (255,0,255,255)
expect(out.pixels[4]).to_equal(255 as u8)
expect(out.pixels[5]).to_equal(0 as u8)
expect(out.pixels[6]).to_equal(255 as u8)
expect(out.pixels[7]).to_equal(255 as u8)
# Blue (0,0,255,255) -> (255,255,0,255)
expect(out.pixels[8]).to_equal(255 as u8)
expect(out.pixels[9]).to_equal(255 as u8)
expect(out.pixels[10]).to_equal(0 as u8)
expect(out.pixels[11]).to_equal(255 as u8)
# White (255,255,255,255) -> (0,0,0,255)
expect(out.pixels[12]).to_equal(0 as u8)
expect(out.pixels[13]).to_equal(0 as u8)
expect(out.pixels[14]).to_equal(0 as u8)
expect(out.pixels[15]).to_equal(255 as u8)
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
