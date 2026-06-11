# Skia Surface Specification

> Tests for SkSurface — the pixel container and canvas factory that mirrors Skia's SkSurface. Covers raster, from-bitmap, and GPU-stub constructors as well as get_canvas, snapshot_bitmap, and clear methods.

<!-- sdn-diagram:id=surface_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=surface_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

surface_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=surface_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Surface Specification

Tests for SkSurface — the pixel container and canvas factory that mirrors Skia's SkSurface. Covers raster, from-bitmap, and GPU-stub constructors as well as get_canvas, snapshot_bitmap, and clear methods.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-SURFACE |
| Category | Stdlib |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/lib/skia/surface_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for SkSurface — the pixel container and canvas factory that mirrors
Skia's SkSurface. Covers raster, from-bitmap, and GPU-stub constructors
as well as get_canvas, snapshot_bitmap, and clear methods.

## Scenarios

### SkSurface construction

#### sk_surface_make_raster: width/height match

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_surface_make_raster(120, 80)
expect(s.width()).to_equal(120)
expect(s.height()).to_equal(80)
```

</details>

#### sk_surface_make_from_bitmap: preserves bitmap dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bmp = Bitmap.zeros(64, 48)
val s = sk_surface_make_from_bitmap(bmp)
expect(s.width()).to_equal(64)
expect(s.height()).to_equal(48)
```

</details>

#### sk_surface_make_gpu_stub: sets backend to GpuStub

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_surface_make_gpu_stub(200, 150)
val is_gpu = s.backend == SurfaceBackend.GpuStub
expect(is_gpu).to_equal(true)
expect(s.width()).to_equal(200)
expect(s.height()).to_equal(150)
```

</details>

### SkSurface methods

#### get_canvas: returns a SkCanvas with matching dimensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_surface_make_raster(100, 50)
val c = s.get_canvas()
expect(c.width).to_equal(100)
expect(c.height).to_equal(50)
```

</details>

#### snapshot_bitmap: returns a clone that's independent of the surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_surface_make_raster(4, 4)
val snap = s.snapshot_bitmap()
expect(snap.width).to_equal(4)
expect(snap.height).to_equal(4)
# Mutate the snapshot and confirm the surface bitmap is unchanged.
snap.pixels[0] = 255 as u8
val orig_byte = s.bitmap.pixels[0] as i64
expect(orig_byte).to_equal(0)
val snap_byte = snap.pixels[0] as i64
expect(snap_byte).to_be_greater_than(0)
```

</details>

#### clear: makes all pixels zero

1. s clear
   - Expected: all_zero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = sk_surface_make_raster(3, 3)
# Dirty a pixel via the underlying bitmap, then clear.
s.bitmap.pixels[0] = 200 as u8
s.bitmap.pixels[5] = 150 as u8
s.clear()
val total = s.bitmap.width * s.bitmap.height * 4
var all_zero = true
var i = 0
while i < total:
    if s.bitmap.pixels[i] != (0 as u8):
        all_zero = false
    i = i + 1
expect(all_zero).to_equal(true)
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
