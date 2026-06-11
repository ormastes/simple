# Skia Color Convert Specification

> Tests for convert_rgba_pixel, convert_bitmap, and convert_pixel_to_srgb — the color-space bitmap-conversion helpers mirroring Chromium's SkColorSpaceXformSteps.

<!-- sdn-diagram:id=color_convert_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=color_convert_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

color_convert_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=color_convert_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Color Convert Specification

Tests for convert_rgba_pixel, convert_bitmap, and convert_pixel_to_srgb — the color-space bitmap-conversion helpers mirroring Chromium's SkColorSpaceXformSteps.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-011 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/color_convert_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for convert_rgba_pixel, convert_bitmap, and convert_pixel_to_srgb — the
color-space bitmap-conversion helpers mirroring Chromium's
SkColorSpaceXformSteps.

## Scenarios

### color_convert

#### convert_rgba_pixel: same space is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cs = srgb()
val out = convert_rgba_pixel(0.25, 0.5, 0.75, 0.8, cs, cs)
val r = out.0
val g = out.1
val b = out.2
val a = out.3
val r_ok = math_abs(r - 0.25) < 1e-6
val g_ok = math_abs(g - 0.5) < 1e-6
val b_ok = math_abs(b - 0.75) < 1e-6
val a_ok = math_abs(a - 0.8) < 1e-6
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a_ok).to_equal(true)
```

</details>

#### convert_rgba_pixel: sRGB to Display P3 preserves alpha exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = srgb()
val dst = display_p3()
val alpha_in = 0.37
val out = convert_rgba_pixel(0.6, 0.2, 0.1, alpha_in, src, dst)
val a_out = out.3
expect(a_out).to_equal(alpha_in)
```

</details>

#### convert_bitmap: returns new bitmap with same dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src_bmp = Bitmap.zeros(4, 3)
val src_space = srgb()
val dst_space = display_p3()
val out_bmp = convert_bitmap(src_bmp, src_space, dst_space)
expect(out_bmp.width).to_equal(4)
expect(out_bmp.height).to_equal(3)
val expected_len = 4 * 3 * 4
expect(out_bmp.pixels.length()).to_equal(expected_len)
```

</details>

#### convert_pixel_to_srgb: from Rec2020 pure red is approximately clamped sRGB red

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rec2020()
val out = convert_pixel_to_srgb(1.0, 0.0, 0.0, 1.0, src)
val r = out.0
val g = out.1
val b = out.2
val a = out.3
# Rec2020 (0,1] primaries are wider than sRGB: pure Rec2020 red, after
# conversion, will have a non-negative red channel and clamped
# (possibly small negative pre-clamp) green/blue in [0,1].
expect(r).to_be_greater_than(0.0)
expect(g).to_be_less_than(1.0)
expect(b).to_be_less_than(1.0)
val r_in_range = r <= 1.0
val g_in_range = g >= 0.0
val b_in_range = b >= 0.0
expect(r_in_range).to_equal(true)
expect(g_in_range).to_equal(true)
expect(b_in_range).to_equal(true)
expect(a).to_equal(1.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
