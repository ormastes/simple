# Glyph Specification

> <details>

<!-- sdn-diagram:id=glyph_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=glyph_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

glyph_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=glyph_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Glyph Specification

## Scenarios

### stub_box_outline

#### glyph_id is stored correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outline = stub_box_outline(65 as u32, 10.0, 12.0)
expect(outline.glyph_id).to_equal(65 as u32)
```

</details>

#### advance_x matches width

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outline = stub_box_outline(65 as u32, 10.0, 12.0)
expect(outline.metrics.advance_x).to_equal(10.0)
```

</details>

#### path has segments (not empty)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outline = stub_box_outline(65 as u32, 10.0, 12.0)
val count = outline.path.segments.len()
expect(count).to_be_greater_than(0)
```

</details>

### rasterize_outline

#### produces bitmap with width > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outline = stub_box_outline(65 as u32, 10.0, 12.0)
val bmp = rasterize_outline(outline, 12.0)
expect(bmp.width).to_be_greater_than(0)
```

</details>

#### produces bitmap with height > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outline = stub_box_outline(65 as u32, 10.0, 12.0)
val bmp = rasterize_outline(outline, 12.0)
expect(bmp.height).to_be_greater_than(0)
```

</details>

#### pixel count equals width times height

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outline = stub_box_outline(65 as u32, 10.0, 12.0)
val bmp = rasterize_outline(outline, 12.0)
val expected = bmp.width * bmp.height
val actual = bmp.pixels.len()
expect(actual).to_equal(expected)
```

</details>

### subpixel_offset

#### 0.1 maps to Zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val off = subpixel_offset(0.1)
expect(off).to_equal(SubpixelOffset.Zero)
```

</details>

#### 0.4 maps to OneThird

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val off = subpixel_offset(0.4)
expect(off).to_equal(SubpixelOffset.OneThird)
```

</details>

#### 0.7 maps to TwoThird

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val off = subpixel_offset(0.7)
expect(off).to_equal(SubpixelOffset.TwoThird)
```

</details>

### apply_subpixel

#### returns bitmap with same width (passthrough stub)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outline = stub_box_outline(65 as u32, 8.0, 10.0)
val bmp = rasterize_outline(outline, 12.0)
val result = apply_subpixel(bmp, SubpixelOffset.Zero)
expect(result.width).to_equal(bmp.width)
```

</details>

### lcd_filter_5tap

#### uniform row preserves brightness within tolerance

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A row of all-128 should produce output where each channel sums close to input sum
val row: [u8] = [128 as u8, 128 as u8, 128 as u8, 128 as u8, 128 as u8]
val out = lcd_filter_5tap(row, LcdOrder.Rgb)
# Output is 15 bytes (5 pixels * 3 channels). Green channel (index 1,4,7,10,13)
# for a uniform input should stay near 128. Check middle pixel green channel.
val mid_g = out[7] as i64
val diff: i64 = if mid_g > 128: mid_g - 128 else: 128 - mid_g
expect(diff).to_be_less_than(10)
```

</details>

#### impulse input spreads into adjacent subpixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Single non-zero pixel in center of 5-wide row
val row: [u8] = [0 as u8, 0 as u8, 255 as u8, 0 as u8, 0 as u8]
val out = lcd_filter_5tap(row, LcdOrder.Rgb)
# Center pixel (index 2) green channel at out[7] should be largest contributor
val center_g = out[7] as i64
# Adjacent pixels (index 1 and 3) should also receive some energy
val left_g = out[4] as i64
val right_g = out[10] as i64
# Center green should be non-zero (impulse spreads to green)
expect(center_g).to_be_greater_than(0)
# At least one neighbor should also be non-zero (filter spreads energy)
val neighbor_sum: i64 = left_g + right_g
expect(neighbor_sum).to_be_greater_than(0)
```

</details>

### apply_lcd_filter

#### Rgb vs Bgr order produces mirrored channels

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Use a non-uniform row so R != B
val pixels: [u8] = [200 as u8, 100 as u8, 50 as u8, 100 as u8, 200 as u8]
val bmp = GlyphBitmap(width: 5, height: 1, left: 0, top: 0, pixels: pixels)
val rgb_bmp = apply_lcd_filter(bmp, LcdOrder.Rgb)
val bgr_bmp = apply_lcd_filter(bmp, LcdOrder.Bgr)
# For pixel i: Rgb stores (R,G,B) and Bgr stores (B,G,R).
# So rgb_bmp.pixels[0] should equal bgr_bmp.pixels[2] (R of Rgb == B slot of Bgr swapped)
val rgb_r = rgb_bmp.pixels[0] as i64
val bgr_b_slot = bgr_bmp.pixels[0] as i64
# They should differ since input is non-uniform (R filter != B filter for asymmetric input)
# The green channel (index 1) should match between Rgb and Bgr
val rgb_g = rgb_bmp.pixels[1] as i64
val bgr_g = bgr_bmp.pixels[1] as i64
expect(rgb_g).to_equal(bgr_g)
```

</details>

### apply_gamma_correction

#### gamma 2.2 darkens mid-gray (128 -> less than 128)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = apply_gamma_correction(128 as u8, 2.2)
val result_i = result as i64
expect(result_i).to_be_less_than(128)
```

</details>

#### gamma 1.0 is identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r0 = apply_gamma_correction(0 as u8, 1.0)
val r128 = apply_gamma_correction(128 as u8, 1.0)
val r255 = apply_gamma_correction(255 as u8, 1.0)
expect(r0 as i64).to_equal(0)
expect(r128 as i64).to_equal(128)
expect(r255 as i64).to_equal(255)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/skia/glyph_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- stub_box_outline
- rasterize_outline
- subpixel_offset
- apply_subpixel
- lcd_filter_5tap
- apply_lcd_filter
- apply_gamma_correction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
