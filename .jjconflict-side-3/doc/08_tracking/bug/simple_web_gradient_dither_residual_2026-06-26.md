# Simple Web Gradient Dither Residual

## Status

Open.

## Problem

Small no-repeat CSS `linear-gradient()` tiles in Simple Web still do not exactly
match Chromium's Skia quantization for every manifest scene. The current
ordered fractional quantization eliminates the `css_box_matrix` residual and
reduces other byte-level color deltas.

## Evidence

Focused `css_box_matrix` bitmap evidence on 2026-06-26:

- Before ordered quantization: 50 mismatches, 50 text/color-delta pixels, 0
  surface-geometry pixels.
- After ordered quantization: 18 mismatches, 18 text/color-delta pixels, 0
  surface-geometry pixels.
- After threshold phase refinement: 0 mismatches, 0 text/color-delta pixels, 0
  surface-geometry pixels.

Additional probes:

- `border_nested_matrix`: 1105 -> 779 mismatches.
- `position_z_index_matrix`: 1833 -> 1708 mismatches.

## Requirement

Production GUI/web renderer parity needs exact layout rows to emit
`mismatch_count=0` and `blur_or_tolerance_used=false`.

## Rejected Shortcuts

- Do not add raw `rt_*` rendering shortcuts.
- Do not use blur/tolerance normalization for exact rows.
- Do not relabel exact manifest rows as tracked without a specific policy and
  gate update that preserves byte-level evidence.

## Next Step

Derive the remaining Chromium/Skia color deltas in the larger nested and
positioned scenes. Fix the underlying selector/layout/color sources where
possible, and split a manifest policy only if the residual is proven to be a
stable Chromium compositor/rasterization difference.
