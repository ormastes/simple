# Skia Resample Specification

> Tests for scale_bitmap with SamplingFilter.{Nearest, Bilinear, Bicubic} — mirroring Chromium/Skia's SkImage::makeScaled + SkSamplingOptions filter modes.

<!-- sdn-diagram:id=resample_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resample_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resample_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resample_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Resample Specification

Tests for scale_bitmap with SamplingFilter.{Nearest, Bilinear, Bicubic} — mirroring Chromium/Skia's SkImage::makeScaled + SkSamplingOptions filter modes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-RESAMPLE |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/resample_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for scale_bitmap with SamplingFilter.{Nearest, Bilinear, Bicubic} —
mirroring Chromium/Skia's SkImage::makeScaled + SkSamplingOptions filter modes.

## Scenarios

### resample

#### scale_bitmap: same-size with Nearest returns equal bitmap

1.
2.
3.
4.
   - Expected: out.width equals `2`
   - Expected: out.height equals `2`
   - Expected: p00.0 equals `10 as i64`
   - Expected: p00.1 equals `20 as i64`
   - Expected: p10.0 equals `100 as i64`
   - Expected: p01.0 equals `50 as i64`
   - Expected: p11.0 equals `200 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2x2 source: distinct colors per pixel
val pattern = [
    (10 as i64, 20 as i64, 30 as i64, 255 as i64),
    (100 as i64, 110 as i64, 120 as i64, 255 as i64),
    (50 as i64, 60 as i64, 70 as i64, 255 as i64),
    (200 as i64, 210 as i64, 220 as i64, 255 as i64),
]
val src = _make_bitmap(2, 2, pattern)
val out = scale_bitmap(src, 2, 2, SamplingFilter.Nearest)
expect(out.width).to_equal(2)
expect(out.height).to_equal(2)
val p00 = _get_rgba(out, 0, 0)
val p10 = _get_rgba(out, 1, 0)
val p01 = _get_rgba(out, 0, 1)
val p11 = _get_rgba(out, 1, 1)
expect(p00.0).to_equal(10 as i64)
expect(p00.1).to_equal(20 as i64)
expect(p10.0).to_equal(100 as i64)
expect(p01.0).to_equal(50 as i64)
expect(p11.0).to_equal(200 as i64)
```

</details>

#### scale_bitmap: 2x2 red upscaled to 4x4 with Bilinear is still red

1.
2.
3.
4.
   - Expected: out.width equals `4`
   - Expected: out.height equals `4`
   - Expected: p.0 equals `255 as i64`
   - Expected: p.1 equals `0 as i64`
   - Expected: p.2 equals `0 as i64`
   - Expected: p.3 equals `255 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pattern = [
    (255 as i64, 0 as i64, 0 as i64, 255 as i64),
    (255 as i64, 0 as i64, 0 as i64, 255 as i64),
    (255 as i64, 0 as i64, 0 as i64, 255 as i64),
    (255 as i64, 0 as i64, 0 as i64, 255 as i64),
]
val src = _make_bitmap(2, 2, pattern)
val out = scale_bitmap(src, 4, 4, SamplingFilter.Bilinear)
expect(out.width).to_equal(4)
expect(out.height).to_equal(4)
var y = 0
while y < 4:
    var x = 0
    while x < 4:
        val p = _get_rgba(out, x, y)
        expect(p.0).to_equal(255 as i64)
        expect(p.1).to_equal(0 as i64)
        expect(p.2).to_equal(0 as i64)
        expect(p.3).to_equal(255 as i64)
        x = x + 1
    y = y + 1
```

</details>

#### scale_bitmap: 4x4 downscaled to 2x2 preserves average color under Bilinear

1. var pattern = [
2. pattern push
   - Expected: out.width equals `2`
   - Expected: out.height equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Uniform gray source 128 — downscale should stay near 128.
var pattern = [(i64, i64, i64, i64)]()
var i = 0
while i < 16:
    pattern.push((128 as i64, 128 as i64, 128 as i64, 255 as i64))
    i = i + 1
val src = _make_bitmap(4, 4, pattern)
val out = scale_bitmap(src, 2, 2, SamplingFilter.Bilinear)
expect(out.width).to_equal(2)
expect(out.height).to_equal(2)
var y = 0
while y < 2:
    var x = 0
    while x < 2:
        val p = _get_rgba(out, x, y)
        val dr = _abs_i64(p.0 - 128)
        val dg = _abs_i64(p.1 - 128)
        val db = _abs_i64(p.2 - 128)
        expect(dr).to_be_less_than(3 as i64)
        expect(dg).to_be_less_than(3 as i64)
        expect(db).to_be_less_than(3 as i64)
        x = x + 1
    y = y + 1
```

</details>

#### scale_bitmap: sharp checkerboard pattern with Bicubic produces smooth transitions (check middle pixel is mixed)

1.
2.
3.
4.
   - Expected: out.width equals `5`
   - Expected: out.height equals `5`
   - Expected: r_in is true
   - Expected: g_in is true
   - Expected: b_in is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2x2 checkerboard: black/white/white/black
val pattern = [
    (0 as i64, 0 as i64, 0 as i64, 255 as i64),
    (255 as i64, 255 as i64, 255 as i64, 255 as i64),
    (255 as i64, 255 as i64, 255 as i64, 255 as i64),
    (0 as i64, 0 as i64, 0 as i64, 255 as i64),
]
val src = _make_bitmap(2, 2, pattern)
# Upscale to 5x5 so the literal center pixel (2,2) sits between samples.
val out = scale_bitmap(src, 5, 5, SamplingFilter.Bicubic)
expect(out.width).to_equal(5)
expect(out.height).to_equal(5)
val mid = _get_rgba(out, 2, 2)
# Bicubic blend of checkerboard at center should be an intermediate gray
# (not pure 0 and not pure 255).
expect(mid.0).to_be_greater_than(30 as i64)
expect(mid.0).to_be_less_than(225 as i64)
# Output channels must stay within [0,255] (bicubic can overshoot before
# the internal clamp).
val r_in = mid.0 >= 0 and mid.0 <= 255
val g_in = mid.1 >= 0 and mid.1 <= 255
val b_in = mid.2 >= 0 and mid.2 <= 255
expect(r_in).to_equal(true)
expect(g_in).to_equal(true)
expect(b_in).to_equal(true)
```

</details>

#### scale_bitmap: Nearest produces a blocky result (check adjacent pixels in scaled output match source)

1.
2.
3.
4.
   - Expected: out.width equals `4`
   - Expected: out.height equals `4`
   - Expected: tl_a.0 equals `tl_b.0`
   - Expected: tl_a.1 equals `tl_b.1`
   - Expected: tl_a.2 equals `tl_b.2`
   - Expected: tl_a.0 equals `255 as i64`
   - Expected: tl_a.1 equals `0 as i64`
   - Expected: tl_a.2 equals `0 as i64`
   - Expected: tr.0 equals `0 as i64`
   - Expected: tr.1 equals `255 as i64`
   - Expected: tr.2 equals `0 as i64`
   - Expected: br.0 equals `255 as i64`
   - Expected: br.1 equals `255 as i64`
   - Expected: br.2 equals `0 as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2x2 source with distinct pure colors in each quadrant.
val pattern = [
    (255 as i64, 0 as i64, 0 as i64, 255 as i64),    # top-left: red
    (0 as i64, 255 as i64, 0 as i64, 255 as i64),    # top-right: green
    (0 as i64, 0 as i64, 255 as i64, 255 as i64),    # bot-left: blue
    (255 as i64, 255 as i64, 0 as i64, 255 as i64),  # bot-right: yellow
]
val src = _make_bitmap(2, 2, pattern)
# Upscale 4x — each source pixel should replicate into a 2x2 block.
val out = scale_bitmap(src, 4, 4, SamplingFilter.Nearest)
expect(out.width).to_equal(4)
expect(out.height).to_equal(4)
# Adjacent pixels inside the same source-cell block must match.
val tl_a = _get_rgba(out, 0, 0)
val tl_b = _get_rgba(out, 1, 0)
expect(tl_a.0).to_equal(tl_b.0)
expect(tl_a.1).to_equal(tl_b.1)
expect(tl_a.2).to_equal(tl_b.2)
# And must equal the source top-left color (red).
expect(tl_a.0).to_equal(255 as i64)
expect(tl_a.1).to_equal(0 as i64)
expect(tl_a.2).to_equal(0 as i64)
# Top-right block (pixel col 2-3, row 0) should be source green.
val tr = _get_rgba(out, 2, 0)
expect(tr.0).to_equal(0 as i64)
expect(tr.1).to_equal(255 as i64)
expect(tr.2).to_equal(0 as i64)
# Bottom-right block (3,3) should be source yellow.
val br = _get_rgba(out, 3, 3)
expect(br.0).to_equal(255 as i64)
expect(br.1).to_equal(255 as i64)
expect(br.2).to_equal(0 as i64)
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
