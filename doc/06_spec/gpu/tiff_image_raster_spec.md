# Tiff Image Raster Specification

## Scenarios

### TIFF image raster

#### renders decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 1, 0) equals `[40, 50, 60, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-spec"))
var surface = GpuSurface.create(1, 2, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x1_rgb())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 1)

expect(pixel(surface, 0, 0)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 1, 0)).to_equal([40, 50, 60, 255])
```

</details>

#### renders multi-strip decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 1, 0) equals `[40, 50, 60, 255]`
   - Expected: pixel(surface, 0, 1) equals `[70, 80, 90, 255]`
   - Expected: pixel(surface, 1, 1) equals `[100, 110, 120, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-multistrip-spec"))
var surface = GpuSurface.create(1, 2, 2, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x2_rgb_two_strips())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 2)

expect(pixel(surface, 0, 0)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 1, 0)).to_equal([40, 50, 60, 255])
expect(pixel(surface, 0, 1)).to_equal([70, 80, 90, 255])
expect(pixel(surface, 1, 1)).to_equal([100, 110, 120, 255])
```

</details>

#### renders tiled decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 1, 0) equals `[40, 50, 60, 255]`
   - Expected: pixel(surface, 0, 1) equals `[70, 80, 90, 255]`
   - Expected: pixel(surface, 1, 1) equals `[100, 110, 120, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-tile-spec"))
var surface = GpuSurface.create(1, 2, 2, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x2_rgb_single_tile())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 2)

expect(pixel(surface, 0, 0)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 1, 0)).to_equal([40, 50, 60, 255])
expect(pixel(surface, 0, 1)).to_equal([70, 80, 90, 255])
expect(pixel(surface, 1, 1)).to_equal([100, 110, 120, 255])
```

</details>

#### renders 16-bit tiled decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[0, 128, 255, 255]`
   - Expected: pixel(surface, 1, 0) equals `[1, 32, 64, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-rgb16-tile-spec"))
var surface = GpuSurface.create(1, 2, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x1_rgb16_single_tile())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 1)

expect(pixel(surface, 0, 0)).to_equal([0, 128, 255, 255])
expect(pixel(surface, 1, 0)).to_equal([1, 32, 64, 255])
```

</details>

#### renders multi-tile decoded TIFF pixels with edge padding exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 1, 0) equals `[40, 50, 60, 255]`
   - Expected: pixel(surface, 2, 0) equals `[70, 80, 90, 255]`
   - Expected: pixel(surface, 0, 1) equals `[100, 110, 120, 255]`
   - Expected: pixel(surface, 1, 1) equals `[30, 40, 50, 255]`
   - Expected: pixel(surface, 2, 1) equals `[60, 70, 80, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-multitile-spec"))
var surface = GpuSurface.create(1, 3, 2, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_3x2_rgb_four_tiles())

rasterizer.raster_draw_image(surface, image, 0, 0, 3, 2)

expect(pixel(surface, 0, 0)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 1, 0)).to_equal([40, 50, 60, 255])
expect(pixel(surface, 2, 0)).to_equal([70, 80, 90, 255])
expect(pixel(surface, 0, 1)).to_equal([100, 110, 120, 255])
expect(pixel(surface, 1, 1)).to_equal([30, 40, 50, 255])
expect(pixel(surface, 2, 1)).to_equal([60, 70, 80, 255])
```

</details>

#### renders PackBits decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 1, 0) equals `[40, 50, 60, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-packbits-spec"))
var surface = GpuSurface.create(1, 2, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x1_rgb_packbits())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 1)

expect(pixel(surface, 0, 0)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 1, 0)).to_equal([40, 50, 60, 255])
```

</details>

#### renders palette ColorMap decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[255, 0, 0, 255]`
   - Expected: pixel(surface, 1, 0) equals `[0, 255, 0, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-palette-spec"))
var surface = GpuSurface.create(1, 2, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x1_palette_red_green())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 1)

expect(pixel(surface, 0, 0)).to_equal([255, 0, 0, 255])
expect(pixel(surface, 1, 0)).to_equal([0, 255, 0, 255])
```

</details>

#### renders planar RGB decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[10, 20, 30, 255]`
   - Expected: pixel(surface, 1, 0) equals `[40, 50, 60, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-planar-spec"))
var surface = GpuSurface.create(1, 2, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x1_planar_rgb())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 1)

expect(pixel(surface, 0, 0)).to_equal([10, 20, 30, 255])
expect(pixel(surface, 1, 0)).to_equal([40, 50, 60, 255])
```

</details>

#### renders 16-bit grayscale decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[0, 0, 0, 255]`
   - Expected: pixel(surface, 1, 0) equals `[255, 255, 255, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-gray16-spec"))
var surface = GpuSurface.create(1, 2, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x1_gray16_black_is_zero())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 1)

expect(pixel(surface, 0, 0)).to_equal([0, 0, 0, 255])
expect(pixel(surface, 1, 0)).to_equal([255, 255, 255, 255])
```

</details>

#### renders 16-bit RGB decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[0, 128, 255, 255]`
   - Expected: pixel(surface, 1, 0) equals `[1, 32, 64, 255]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-rgb16-spec"))
var surface = GpuSurface.create(1, 2, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_2x1_rgb16())

rasterizer.raster_draw_image(surface, image, 0, 0, 2, 1)

expect(pixel(surface, 0, 0)).to_equal([0, 128, 255, 255])
expect(pixel(surface, 1, 0)).to_equal([1, 32, 64, 255])
```

</details>

#### renders 16-bit RGBA decoded TIFF pixels through the raster image path exactly

1. var rasterizer = Rasterizer new

2. var surface = GpuSurface create

3. rasterizer raster draw image
   - Expected: pixel(surface, 0, 0) equals `[0, 16, 32, 64]`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rasterizer = Rasterizer.new(Logger.new("tiff-raster-rgba16-spec"))
var surface = GpuSurface.create(1, 1, 1, SurfaceFormat.RGBA8)
val image = decode_tiff(_tiff_le_1x1_rgba16())

rasterizer.raster_draw_image(surface, image, 0, 0, 1, 1)

expect(pixel(surface, 0, 0)).to_equal([0, 16, 32, 64])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | GPU & SIMD |
| Status | Active |
| Source | `examples/browser/test/gpu/tiff_image_raster_spec.spl` |
| Updated | 2026-05-31 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TIFF image raster

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

