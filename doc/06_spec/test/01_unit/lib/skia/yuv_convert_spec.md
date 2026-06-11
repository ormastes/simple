# Skia YUV Convert Specification

> Tests for yuv_to_rgb, rgb_to_yuv, and yuv_bitmap_to_rgba -- the YUV color conversion helpers mirroring Skia's SkYUVAInfo YUV-to-RGB math.

<!-- sdn-diagram:id=yuv_convert_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=yuv_convert_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

yuv_convert_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=yuv_convert_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia YUV Convert Specification

Tests for yuv_to_rgb, rgb_to_yuv, and yuv_bitmap_to_rgba -- the YUV color conversion helpers mirroring Skia's SkYUVAInfo YUV-to-RGB math.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-012 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/yuv_convert_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for yuv_to_rgb, rgb_to_yuv, and yuv_bitmap_to_rgba -- the YUV color
conversion helpers mirroring Skia's SkYUVAInfo YUV-to-RGB math.

## Scenarios

### yuv_convert

#### yuv_to_rgb: BT.601 full-range pure-gray Y=0.5, U=0.5, V=0.5 -> RGB=(0.5, 0.5, 0.5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rgb = yuv_to_rgb(0.5, 0.5, 0.5, YuvMatrix.BT601, YuvRange.Full)
val r = rgb.0
val g = rgb.1
val b = rgb.2
val r_ok = math_abs(r - 0.5) < 1e-6
val g_ok = math_abs(g - 0.5) < 1e-6
val b_ok = math_abs(b - 0.5) < 1e-6
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
```

</details>

#### yuv_to_rgb: BT.709 pure red round-trips via rgb_to_yuv

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val yuv = rgb_to_yuv(1.0, 0.0, 0.0, YuvMatrix.BT709, YuvRange.Full)
val y = yuv.0
val u = yuv.1
val v = yuv.2
val rgb = yuv_to_rgb(y, u, v, YuvMatrix.BT709, YuvRange.Full)
val r = rgb.0
val g = rgb.1
val b = rgb.2
val r_ok = math_abs(r - 1.0) < 1e-3
val g_ok = math_abs(g - 0.0) < 1e-3
val b_ok = math_abs(b - 0.0) < 1e-3
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
```

</details>

#### rgb_to_yuv -> yuv_to_rgb round-trip preserves RGB within 1e-3

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val yuv = rgb_to_yuv(0.3, 0.6, 0.2, YuvMatrix.BT601, YuvRange.Full)
val y = yuv.0
val u = yuv.1
val v = yuv.2
val rgb = yuv_to_rgb(y, u, v, YuvMatrix.BT601, YuvRange.Full)
val r = rgb.0
val g = rgb.1
val b = rgb.2
val r_ok = math_abs(r - 0.3) < 1e-3
val g_ok = math_abs(g - 0.6) < 1e-3
val b_ok = math_abs(b - 0.2) < 1e-3
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
```

</details>

#### yuv_to_rgb: output clamps to [0, 1] -- extreme inputs don't overshoot

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Extreme UV should push channels outside [0,1] before clamping.
val rgb_high = yuv_to_rgb(1.0, 1.0, 1.0, YuvMatrix.BT601, YuvRange.Full)
val rgb_low  = yuv_to_rgb(0.0, 0.0, 0.0, YuvMatrix.BT601, YuvRange.Full)
expect(rgb_high.0).to_be_less_than(1.0 + 1e-9)
expect(rgb_high.1).to_be_less_than(1.0 + 1e-9)
expect(rgb_high.2).to_be_less_than(1.0 + 1e-9)
expect(rgb_high.0).to_be_greater_than(0.0 - 1e-9)
expect(rgb_high.1).to_be_greater_than(0.0 - 1e-9)
expect(rgb_high.2).to_be_greater_than(0.0 - 1e-9)
expect(rgb_low.0).to_be_less_than(1.0 + 1e-9)
expect(rgb_low.1).to_be_less_than(1.0 + 1e-9)
expect(rgb_low.2).to_be_less_than(1.0 + 1e-9)
expect(rgb_low.0).to_be_greater_than(0.0 - 1e-9)
expect(rgb_low.1).to_be_greater_than(0.0 - 1e-9)
expect(rgb_low.2).to_be_greater_than(0.0 - 1e-9)
```

</details>

#### yuv_bitmap_to_rgba: dimension mismatch returns empty bitmap

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val yp = Bitmap.zeros(4, 4)
val up = Bitmap.zeros(4, 4)
val vp = Bitmap.zeros(3, 4)
val out = yuv_bitmap_to_rgba(yp, up, vp, YuvMatrix.BT601, YuvRange.Full)
expect(out.width).to_equal(0)
expect(out.height).to_equal(0)
```

</details>

#### yuv_bitmap_to_rgba: uniform Y=U=V=0.5 input produces roughly uniform gray output

1. yp set pixel
2. up set pixel
3. vp set pixel
   - Expected: out.width equals `w`
   - Expected: out.height equals `h`
   - Expected: r_ok is true
   - Expected: g_ok is true
   - Expected: b_ok is true
   - Expected: a0 equals `255 as u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = 2
val h = 2
val yp = Bitmap.zeros(w, h)
val up = Bitmap.zeros(w, h)
val vp = Bitmap.zeros(w, h)
# Fill each plane's channel 0 with 128 (~0.5)
var py = 0
while py < h:
    var px = 0
    while px < w:
        val gray = SkColor4f(r: 0.5, g: 0.0, b: 0.0, a: 0.0)
        yp.set_pixel(px, py, gray)
        up.set_pixel(px, py, gray)
        vp.set_pixel(px, py, gray)
        px = px + 1
    py = py + 1
val out = yuv_bitmap_to_rgba(yp, up, vp, YuvMatrix.BT601, YuvRange.Full)
expect(out.width).to_equal(w)
expect(out.height).to_equal(h)
# Sample (0,0) -- expect R,G,B all near 0.5 (which is ~128/255)
val r0 = out.pixels[0]
val g0 = out.pixels[1]
val b0 = out.pixels[2]
val a0 = out.pixels[3]
val r_ok = math_abs((r0 as f64) - 128.0) < 4.0
val g_ok = math_abs((g0 as f64) - 128.0) < 4.0
val b_ok = math_abs((b0 as f64) - 128.0) < 4.0
expect(r_ok).to_equal(true)
expect(g_ok).to_equal(true)
expect(b_ok).to_equal(true)
expect(a0).to_equal(255 as u8)
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
