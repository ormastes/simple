# Skia CPU Blend Modes, SaveLayer Isolation, and 3x3 Affine Matrix Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 4 | 4 | 0 | 0 |

## Overview

Verifies `REQ-S2D-005..007` and `NFR-S2D-002`: lossless 3x3 affine shear/skew
preservation across `SkCanvas` recording and `CpuBackend` replay, isolated
offscreen `SaveLayer` / `Restore` compositing, and non-`SrcOver` `SkBlendMode`
evaluation on `DrawImage` and `DrawPath`.

## Scenarios

### Lossless shear/skew transform via SkCanvas.concat

1. Record a `4x8` rectangle under a `0.5` x-shear matrix via `SkCanvas.concat`.
2. Render with `cpu_backend_new().render_picture`.
   - Expected: pixel `(5, 6)` is filled and `(1, 6)` remains transparent.

### SaveLayer isolation with overlapping children

1. Paint two overlapping opaque red rectangles inside an alpha-128 `SaveLayer` over opaque blue.
   - Expected: overlap `(4, 4)` matches single-rect `(2, 2)` (`[100, 0, 100, 255]`), proving layer alpha applies once at `Restore`.

### DrawImage Multiply against destination pixels

1. Draw a translucent `2x2` image with `SkBlendMode.Multiply` over cornflower blue.
   - Expected: destination pixels are read and blended to `[43, 126, 103, 255]` (`+-2` LSB).

### DrawPath Darken blend mode

1. Draw a blue triangle path with `SkBlendMode.Darken` over yellow.
   - Expected: interior pixel `(6, 2)` is `[0, 100, 0, 255]`.

## Source

- Executable spec: `test/01_unit/lib/skia/cpu_backend_blend_layer_matrix_spec.spl`
