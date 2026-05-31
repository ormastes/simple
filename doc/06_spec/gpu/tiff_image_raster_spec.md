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
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

