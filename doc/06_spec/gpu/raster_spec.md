# Raster Specification

## Scenarios

### Rasterizer

### DrawText

#### rasterizes bitmap glyphs instead of solid character blocks

1. var rasterizer = make rasterizer

2. var surface = GpuSurface create

3. rasterizer raster draw text
   - Expected: pixel(surface, 2, 1) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 1, 1) equals `[0, 0, 0, 0]`
   - Expected: pixel(surface, 3, 3) equals `[0, 0, 0, 0]`
   - Expected: pixel(surface, 1, 4) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 5, 4) equals `[10, 20, 30, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = make_rasterizer()
var surface = GpuSurface.create(1, 8, 9, SurfaceFormat.RGBA8)

rasterizer.raster_draw_text(surface, 1, 8, "A", 7.0, raster_color_rgba(10, 20, 30, 255))

expect(pixel(surface, 2, 1)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 1, 1)).to_equal([0, 0, 0, 0])
expect(pixel(surface, 3, 3)).to_equal([0, 0, 0, 0])
expect(pixel(surface, 1, 4)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 5, 4)).to_equal([10, 20, 30, 255])
```

</details>

#### renders lowercase letters using their alphabetic glyphs

1. var rasterizer = make rasterizer

2. var surface = GpuSurface create

3. rasterizer raster draw text
   - Expected: pixel(surface, 1, 1) equals `[0, 0, 0, 0]`
   - Expected: pixel(surface, 5, 1) equals `[1, 2, 3, 255]`
   - Expected: pixel(surface, 4, 4) equals `[1, 2, 3, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = make_rasterizer()
var surface = GpuSurface.create(1, 8, 9, SurfaceFormat.RGBA8)

rasterizer.raster_draw_text(surface, 1, 8, "g", 7.0, raster_color_rgba(1, 2, 3, 255))

expect(pixel(surface, 1, 1)).to_equal([0, 0, 0, 0])
expect(pixel(surface, 5, 1)).to_equal([1, 2, 3, 255])
expect(pixel(surface, 4, 4)).to_equal([1, 2, 3, 255])
```

</details>

### DrawImage

#### rasterizes registered decoded images from display list items

1. var rasterizer = make rasterizer

2. var surface = GpuSurface create

3. rasterizer register image
   - Expected: result.? is true
   - Expected: pixel(surface, 0, 0) equals `[255, 0, 0, 255]`
   - Expected: pixel(surface, 1, 0) equals `[0, 255, 0, 255]`
   - Expected: pixel(surface, 0, 1) equals `[0, 0, 255, 255]`
   - Expected: pixel(surface, 1, 1) equals `[255, 255, 255, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = make_rasterizer()
var surface = GpuSurface.create(1, 2, 2, SurfaceFormat.RGBA8)
rasterizer.register_image(9, two_by_two_image())
val item = DisplayItem.create(0, PaintOp.DrawImage(0.0, 0.0, 2.0, 2.0, 9, "asset.bmp"))

val result = rasterizer.rasterize([item], surface)
expect(result.?).to_equal(true)
expect(pixel(surface, 0, 0)).to_equal([255, 0, 0, 255])
expect(pixel(surface, 1, 0)).to_equal([0, 255, 0, 255])
expect(pixel(surface, 0, 1)).to_equal([0, 0, 255, 255])
expect(pixel(surface, 1, 1)).to_equal([255, 255, 255, 255])
```

</details>

#### leaves target unchanged when image id is missing

1. var rasterizer = make rasterizer

2. var surface = GpuSurface create
   - Expected: result.? is true
   - Expected: pixel(surface, 0, 0) equals `[0, 0, 0, 0]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = make_rasterizer()
var surface = GpuSurface.create(1, 1, 1, SurfaceFormat.RGBA8)
val item = DisplayItem.create(0, PaintOp.DrawImage(0.0, 0.0, 1.0, 1.0, 404, "missing.bmp"))

val result = rasterizer.rasterize([item], surface)
expect(result.?).to_equal(true)
expect(pixel(surface, 0, 0)).to_equal([0, 0, 0, 0])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `examples/11_advanced/browser/test/gpu/raster_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Rasterizer
- DrawText
- DrawImage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

