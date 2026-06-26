# Electron Simple Web Layout Gradient Dither Evidence - 2026-06-26

## Summary

Small no-repeat CSS gradient tiles now use ordered fractional quantization in
the Simple Web layout renderer. This moves the renderer closer to Chromium's
Skia output without adding blur/tolerance, raw runtime shortcuts, or changing
large repeated gradient fills.

## Focused Evidence

Command:

```sh
BUILD_DIR=build/test-css-box-gradient-dither \
REPORT_PATH=build/test-css-box-gradient-dither/report.md \
ELECTRON_BITMAP_SCENE=simple-web-layout-css-box-matrix \
ELECTRON_BITMAP_WIDTH=96 \
ELECTRON_BITMAP_HEIGHT=64 \
ELECTRON_BITMAP_TIMEOUT_SECS=30 \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

Result after the renderer change:

- `electron_simple_web_layout_status=divergent`
- `electron_simple_web_layout_reason=checksum-mismatch`
- `electron_simple_web_layout_mismatch_count=18`
- `electron_simple_web_layout_text_color_delta_pixels=18`
- `electron_simple_web_layout_surface_geometry_pixels=0`
- `electron_simple_web_layout_blur_or_tolerance_used=false`

Previous production evidence for the same case:

- `electron_simple_web_layout_mismatch_count=50`
- `electron_simple_web_layout_text_color_delta_pixels=50`
- `electron_simple_web_layout_surface_geometry_pixels=0`

The change reduces the smallest exact layout mismatch from 50 to 18 pixels. It
does not make the manifest pass yet.

## Broader Probe

Additional probes remained divergent but improved slightly:

- `border_nested_matrix`: 1105 -> 1065 mismatches.
- `position_z_index_matrix`: 1833 -> 1788 mismatches.

Both still report `surface_geometry_pixels=0`, so the remaining blocker is
gradient/color quantization, not layout geometry.

## Tests

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --clean`
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl --mode=interpreter --clean`
- `bin/simple spipe-docgen test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --output doc/06_spec --no-index`

## Remaining Work

The residual 18-pixel `css_box_matrix` mismatch shows the ordered quantization
phase/threshold still does not exactly match Chromium. Full production
GUI/web parity remains incomplete until the exact layout cases reach
`mismatch_count=0` or the manifest explicitly records a narrower tracked
Chromium-dither policy with a release gate that still forbids blur/tolerance.
