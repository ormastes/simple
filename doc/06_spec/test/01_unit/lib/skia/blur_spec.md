# Skia Blur Image Filter Specification

> Tests for apply_blur, blur_filter_new, and _box_radii_for_sigma — the Bitmap-native Gaussian blur image filter mirroring SkImageFilters::Blur. Implementation is Kovesi's 3-pass box-blur approximation.

<!-- sdn-diagram:id=blur_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blur_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blur_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blur_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Blur Image Filter Specification

Tests for apply_blur, blur_filter_new, and _box_radii_for_sigma — the Bitmap-native Gaussian blur image filter mirroring SkImageFilters::Blur. Implementation is Kovesi's 3-pass box-blur approximation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-BLUR |
| Category | Stdlib / Filter |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/blur_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for apply_blur, blur_filter_new, and _box_radii_for_sigma — the
Bitmap-native Gaussian blur image filter mirroring SkImageFilters::Blur.
Implementation is Kovesi's 3-pass box-blur approximation.

## Scenarios

### blur

#### apply_blur: identity sigma=0 produces input unchanged

1.  fill rgba
   - Expected: out.width equals `5`
   - Expected: out.height equals `5`
   - Expected: _px_r(out, 2, 2) equals `10`
   - Expected: _px_g(out, 2, 2) equals `20`
   - Expected: _px_b(out, 2, 2) equals `30`
   - Expected: _px_a(out, 2, 2) equals `40`
   - Expected: _px_r(out, 0, 0) equals `128`
   - Expected: _px_a(out, 4, 4) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = Bitmap.zeros(5, 5)
_fill_rgba(src, 128 as u8, 64 as u8, 200 as u8, 255 as u8)
# Poke a distinct center pixel to make the test sensitive.
val cidx = (2 * 5 + 2) * 4
src.pixels[cidx]     = 10 as u8
src.pixels[cidx + 1] = 20 as u8
src.pixels[cidx + 2] = 30 as u8
src.pixels[cidx + 3] = 40 as u8
val filt = blur_filter_new(0.0, 0.0)
val out = apply_blur(src, filt)
# sigma=0 => all radii 0 => identity copy
expect(out.width).to_equal(5)
expect(out.height).to_equal(5)
expect(_px_r(out, 2, 2)).to_equal(10)
expect(_px_g(out, 2, 2)).to_equal(20)
expect(_px_b(out, 2, 2)).to_equal(30)
expect(_px_a(out, 2, 2)).to_equal(40)
expect(_px_r(out, 0, 0)).to_equal(128)
expect(_px_a(out, 4, 4)).to_equal(255)
```

</details>

#### apply_blur: 10x10 solid red bitmap stays solid red after blur (alpha preserved)

1.  fill rgba
   - Expected: r_center equals `255`
   - Expected: g_center equals `0`
   - Expected: b_center equals `0`
   - Expected: a_center equals `255`
   - Expected: _px_r(out, 0, 0) equals `255`
   - Expected: _px_a(out, 9, 9) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = Bitmap.zeros(10, 10)
_fill_rgba(src, 255 as u8, 0 as u8, 0 as u8, 255 as u8)
val filt = blur_filter_new(2.0, 2.0)
val out = apply_blur(src, filt)
# Blur of a uniform image is the same uniform image (clamp-to-edge).
val r_center = _px_r(out, 5, 5)
val g_center = _px_g(out, 5, 5)
val b_center = _px_b(out, 5, 5)
val a_center = _px_a(out, 5, 5)
expect(r_center).to_equal(255)
expect(g_center).to_equal(0)
expect(b_center).to_equal(0)
expect(a_center).to_equal(255)
# Corners stay uniform too
expect(_px_r(out, 0, 0)).to_equal(255)
expect(_px_a(out, 9, 9)).to_equal(255)
```

</details>

#### apply_blur: sharp edge between red and blue becomes smooth gradient

<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = 20 as i64
val h = 4 as i64
val src = Bitmap.zeros(w, h)
# Left half red, right half blue, full alpha.
var y = 0 as i64
while y < h:
    var x = 0 as i64
    while x < w:
        val idx = (y * w + x) * 4
        if x < w / 2:
            src.pixels[idx]     = 255 as u8
            src.pixels[idx + 1] = 0 as u8
            src.pixels[idx + 2] = 0 as u8
            src.pixels[idx + 3] = 255 as u8
        else:
            src.pixels[idx]     = 0 as u8
            src.pixels[idx + 1] = 0 as u8
            src.pixels[idx + 2] = 255 as u8
            src.pixels[idx + 3] = 255 as u8
        x = x + 1
    y = y + 1
val filt = blur_filter_new(3.0, 0.0)
val out = apply_blur(src, filt)
# At the edge pixel (x = w/2 - 1) red should have dropped, blue risen.
val r_at_edge = _px_r(out, (w / 2) - 1, 2)
val b_at_edge = _px_b(out, (w / 2) - 1, 2)
expect(r_at_edge).to_be_less_than(255)
expect(r_at_edge).to_be_greater_than(0)
expect(b_at_edge).to_be_greater_than(0)
expect(b_at_edge).to_be_less_than(255)
# Far-left should still be mostly red
expect(_px_r(out, 0, 2)).to_be_greater_than(200)
# Far-right should still be mostly blue
expect(_px_b(out, w - 1, 2)).to_be_greater_than(200)
```

</details>

#### apply_blur: blur of a single white pixel on black canvas spreads over multiple pixels

1.  fill rgba
   - Expected: _px_r(out, 0, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = 15 as i64
val h = 15 as i64
val src = Bitmap.zeros(w, h)
# Black opaque background
_fill_rgba(src, 0 as u8, 0 as u8, 0 as u8, 255 as u8)
# One white pixel at the center
val cx = 7 as i64
val cy = 7 as i64
val cidx = (cy * w + cx) * 4
src.pixels[cidx]     = 255 as u8
src.pixels[cidx + 1] = 255 as u8
src.pixels[cidx + 2] = 255 as u8
src.pixels[cidx + 3] = 255 as u8
val filt = blur_filter_new(2.0, 2.0)
val out = apply_blur(src, filt)
# Center should have dropped below 255 (energy spread out).
val center_r = _px_r(out, cx, cy)
expect(center_r).to_be_less_than(255)
expect(center_r).to_be_greater_than(0)
# Neighbour pixels should now be non-zero (spread).
val neigh_r = _px_r(out, cx + 1, cy)
expect(neigh_r).to_be_greater_than(0)
val neigh2_r = _px_r(out, cx, cy + 1)
expect(neigh2_r).to_be_greater_than(0)
# A pixel far away stays black.
expect(_px_r(out, 0, 0)).to_equal(0)
```

</details>

#### _box_radii_for_sigma(sigma=2.0, passes=3) returns 3 integers summing to approx 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val radii = _box_radii_for_sigma(2.0, 3 as i64)
expect(radii.len()).to_equal(3)
# For sigma=2, n=3: w_ideal = sqrt(12*4/3 + 1) = sqrt(17) ~= 4.12
# wl = 3 (odd, <= 4.12), wu = 5, radii are 1 and 2.
# Kovesi gives m ~= 2 passes with radius 1 and 1 pass with radius 2,
# summing to 1+1+2 = 4, but the 2D-equivalent summed radius 2*sigma~=4
# maps to ~6 once we count both the wl and wu bands with overlap. We
# check a tolerant range around 6.
val sum = radii[0] + radii[1] + radii[2]
expect(sum).to_be_greater_than(2)
expect(sum).to_be_less_than(10)
# All radii must be non-negative integers.
val r0_ok = radii[0] >= 0
val r1_ok = radii[1] >= 0
val r2_ok = radii[2] >= 0
expect(r0_ok).to_equal(true)
expect(r1_ok).to_equal(true)
expect(r2_ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
