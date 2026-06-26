# Simple Web Gradient Dither Residual

## Status

Open.

## Problem

Small no-repeat CSS `linear-gradient()` tiles in Simple Web still do not exactly
match Chromium's Skia quantization. The current ordered fractional quantization
reduces but does not eliminate byte-level color deltas.

## Evidence

Focused `css_box_matrix` bitmap evidence on 2026-06-26:

- Before ordered quantization: 50 mismatches, 50 text/color-delta pixels, 0
  surface-geometry pixels.
- After ordered quantization: 18 mismatches, 18 text/color-delta pixels, 0
  surface-geometry pixels.

Additional probes:

- `border_nested_matrix`: 1105 -> 1065 mismatches.
- `position_z_index_matrix`: 1833 -> 1788 mismatches.

## Requirement

Production GUI/web renderer parity needs exact layout rows to emit
`mismatch_count=0` and `blur_or_tolerance_used=false`.

## Rejected Shortcuts

- Do not add raw `rt_*` rendering shortcuts.
- Do not use blur/tolerance normalization for exact rows.
- Do not relabel exact manifest rows as tracked without a specific policy and
  gate update that preserves byte-level evidence.

## Next Step

Derive the remaining Chromium/Skia dither phase from captured ARGB rows and
replace the approximate ordered matrix with the exact phase/threshold model, or
split the manifest policy only if the residual is proven to be a stable
Chromium compositor/rasterization difference.
