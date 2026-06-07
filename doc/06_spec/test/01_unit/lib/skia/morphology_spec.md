# Skia Morphology Image Filter Specification

> Tests for apply_morphology, erode_filter_new, and dilate_filter_new — the Bitmap-native erode/dilate image filters mirroring SkImageFilters::Erode and SkImageFilters::Dilate. Implementation is the separable min/max pass (horizontal then vertical) over clamp-to-edge borders, per channel.

<!-- sdn-diagram:id=morphology_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=morphology_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

morphology_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=morphology_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Morphology Image Filter Specification

Tests for apply_morphology, erode_filter_new, and dilate_filter_new — the Bitmap-native erode/dilate image filters mirroring SkImageFilters::Erode and SkImageFilters::Dilate. Implementation is the separable min/max pass (horizontal then vertical) over clamp-to-edge borders, per channel.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-MORPH |
| Category | Stdlib / Filter |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/morphology_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for apply_morphology, erode_filter_new, and dilate_filter_new — the
Bitmap-native erode/dilate image filters mirroring SkImageFilters::Erode
and SkImageFilters::Dilate. Implementation is the separable min/max pass
(horizontal then vertical) over clamp-to-edge borders, per channel.

## Scenarios

### morphology

#### Erode: on uniform red bitmap stays uniform red

1.  fill rgba
   - Expected: out.width equals `8`
   - Expected: out.height equals `8`
   - Expected: _px_r(out, 4, 4) equals `255`
   - Expected: _px_g(out, 4, 4) equals `0`
   - Expected: _px_b(out, 4, 4) equals `0`
   - Expected: _px_a(out, 4, 4) equals `255`
   - Expected: _px_r(out, 0, 0) equals `255`
   - Expected: _px_a(out, 7, 7) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = Bitmap.zeros(8, 8)
_fill_rgba(src, 255 as u8, 0 as u8, 0 as u8, 255 as u8)
val filt = erode_filter_new(2 as i64, 2 as i64)
val out = apply_morphology(src, filt)
expect(out.width).to_equal(8)
expect(out.height).to_equal(8)
expect(_px_r(out, 4, 4)).to_equal(255)
expect(_px_g(out, 4, 4)).to_equal(0)
expect(_px_b(out, 4, 4)).to_equal(0)
expect(_px_a(out, 4, 4)).to_equal(255)
# Corners are also unchanged under clamp-to-edge.
expect(_px_r(out, 0, 0)).to_equal(255)
expect(_px_a(out, 7, 7)).to_equal(255)
```

</details>

#### Dilate: on uniform red bitmap stays uniform red

1.  fill rgba
   - Expected: _px_r(out, 4, 4) equals `255`
   - Expected: _px_g(out, 4, 4) equals `0`
   - Expected: _px_b(out, 4, 4) equals `0`
   - Expected: _px_a(out, 4, 4) equals `255`
   - Expected: _px_r(out, 0, 0) equals `255`
   - Expected: _px_a(out, 7, 7) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = Bitmap.zeros(8, 8)
_fill_rgba(src, 255 as u8, 0 as u8, 0 as u8, 255 as u8)
val filt = dilate_filter_new(2 as i64, 2 as i64)
val out = apply_morphology(src, filt)
expect(_px_r(out, 4, 4)).to_equal(255)
expect(_px_g(out, 4, 4)).to_equal(0)
expect(_px_b(out, 4, 4)).to_equal(0)
expect(_px_a(out, 4, 4)).to_equal(255)
expect(_px_r(out, 0, 0)).to_equal(255)
expect(_px_a(out, 7, 7)).to_equal(255)
```

</details>

#### Erode: single white pixel on black canvas becomes all-black after erode with radius 1

1.  fill rgba
   - Expected: _px_r(out, cx, cy) equals `0`
   - Expected: _px_g(out, cx, cy) equals `0`
   - Expected: _px_b(out, cx, cy) equals `0`
   - Expected: _px_r(out, 0, 0) equals `0`
   - Expected: _px_r(out, 6, 6) equals `0`
   - Expected: _px_a(out, cx, cy) equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = 7 as i64
val h = 7 as i64
val src = Bitmap.zeros(w, h)
_fill_rgba(src, 0 as u8, 0 as u8, 0 as u8, 255 as u8)
# One white pixel at center.
val cx = 3 as i64
val cy = 3 as i64
val cidx = (cy * w + cx) * 4
src.pixels[cidx]     = 255 as u8
src.pixels[cidx + 1] = 255 as u8
src.pixels[cidx + 2] = 255 as u8
src.pixels[cidx + 3] = 255 as u8
val filt = erode_filter_new(1 as i64, 1 as i64)
val out = apply_morphology(src, filt)
# Every output pixel's 3x3 window contains at least one black neighbour,
# so RGB should be 0 everywhere (alpha stays 255 because the white
# pixel's alpha matches the background).
expect(_px_r(out, cx, cy)).to_equal(0)
expect(_px_g(out, cx, cy)).to_equal(0)
expect(_px_b(out, cx, cy)).to_equal(0)
expect(_px_r(out, 0, 0)).to_equal(0)
expect(_px_r(out, 6, 6)).to_equal(0)
# Alpha unchanged (uniform 255 in input).
expect(_px_a(out, cx, cy)).to_equal(255)
```

</details>

#### Dilate: single white pixel on black canvas expands to 3x3 white after dilate with radius 1

1.  fill rgba
   - Expected: _px_r(out, xx, yy) equals `255`
   - Expected: _px_g(out, xx, yy) equals `255`
   - Expected: _px_b(out, xx, yy) equals `255`
   - Expected: _px_r(out, cx + 2, cy) equals `0`
   - Expected: _px_r(out, cx, cy + 2) equals `0`
   - Expected: _px_r(out, 0, 0) equals `0`
2.
3.


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = 7 as i64
val h = 7 as i64
val src = Bitmap.zeros(w, h)
_fill_rgba(src, 0 as u8, 0 as u8, 0 as u8, 255 as u8)
val cx = 3 as i64
val cy = 3 as i64
val cidx = (cy * w + cx) * 4
src.pixels[cidx]     = 255 as u8
src.pixels[cidx + 1] = 255 as u8
src.pixels[cidx + 2] = 255 as u8
src.pixels[cidx + 3] = 255 as u8
val filt = dilate_filter_new(1 as i64, 1 as i64)
val out = apply_morphology(src, filt)
# The 3x3 neighbourhood of the center pixel should all be white.
var yy = cy - 1
while yy <= cy + 1:
    var xx = cx - 1
    while xx <= cx + 1:
        expect(_px_r(out, xx, yy)).to_equal(255)
        expect(_px_g(out, xx, yy)).to_equal(255)
        expect(_px_b(out, xx, yy)).to_equal(255)
        xx = xx + 1
    yy = yy + 1
# Pixels two away stay black.
expect(_px_r(out, cx + 2, cy)).to_equal(0)
expect(_px_r(out, cx, cy + 2)).to_equal(0)
expect(_px_r(out, 0, 0)).to_equal(0)
# The single white pixel's 3x3 region grew, so the total number of
# white center-row pixels is at least 3.
val row_white = (if _px_r(out, cx - 1, cy) == 255: 1 else: 0) +
                (if _px_r(out, cx,     cy) == 255: 1 else: 0) +
                (if _px_r(out, cx + 1, cy) == 255: 1 else: 0)
expect(row_white).to_be_greater_than(2)
expect(row_white).to_be_less_than(4)
```

</details>

#### Erode/Dilate: radius 0 returns input unchanged

1. src pixels[idx]     =
2. src pixels[idx + 1] =
3. src pixels[idx + 2] =
   - Expected: _px_r(eo, 0, 0) equals `_px_r(src, 0, 0)`
   - Expected: _px_g(eo, 1, 2) equals `_px_g(src, 1, 2)`
   - Expected: _px_b(eo, 3, 3) equals `_px_b(src, 3, 3)`
   - Expected: _px_a(eo, 2, 1) equals `_px_a(src, 2, 1)`
   - Expected: _px_r(od, 0, 0) equals `_px_r(src, 0, 0)`
   - Expected: _px_g(od, 1, 2) equals `_px_g(src, 1, 2)`
   - Expected: _px_b(od, 3, 3) equals `_px_b(src, 3, 3)`
   - Expected: _px_a(od, 2, 1) equals `_px_a(src, 2, 1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = 4 as i64
val h = 4 as i64
val src = Bitmap.zeros(w, h)
# Fill with a gradient so we can detect any change.
var i = 0 as i64
val total = w * h
while i < total:
    val idx = i * 4
    src.pixels[idx]     = (i * 7) as u8
    src.pixels[idx + 1] = (i * 11) as u8
    src.pixels[idx + 2] = (i * 13) as u8
    src.pixels[idx + 3] = 255 as u8
    i = i + 1
val ef = erode_filter_new(0 as i64, 0 as i64)
val df = dilate_filter_new(0 as i64, 0 as i64)
val eo = apply_morphology(src, ef)
val od = apply_morphology(src, df)
# Spot-check several positions — both outputs must match input exactly.
expect(_px_r(eo, 0, 0)).to_equal(_px_r(src, 0, 0))
expect(_px_g(eo, 1, 2)).to_equal(_px_g(src, 1, 2))
expect(_px_b(eo, 3, 3)).to_equal(_px_b(src, 3, 3))
expect(_px_a(eo, 2, 1)).to_equal(_px_a(src, 2, 1))
expect(_px_r(od, 0, 0)).to_equal(_px_r(src, 0, 0))
expect(_px_g(od, 1, 2)).to_equal(_px_g(src, 1, 2))
expect(_px_b(od, 3, 3)).to_equal(_px_b(src, 3, 3))
expect(_px_a(od, 2, 1)).to_equal(_px_a(src, 2, 1))
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
