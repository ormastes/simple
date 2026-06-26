# Electron Simple Web Layout Gradient Dither Evidence - 2026-06-26

## Summary

Small no-repeat CSS gradient tiles now use ordered fractional quantization in
the Simple Web layout renderer. This moves the renderer closer to Chromium's
Skia output without adding blur/tolerance, raw runtime shortcuts, or changing
large repeated gradient fills.

## Focused Evidence

Command:

```sh
BUILD_DIR=build/test-css-box-gradient-dither-exact \
REPORT_PATH=build/test-css-box-gradient-dither-exact/report.md \
ELECTRON_BITMAP_SCENE=simple-web-layout-css-box-matrix \
ELECTRON_BITMAP_WIDTH=96 \
ELECTRON_BITMAP_HEIGHT=64 \
ELECTRON_BITMAP_TIMEOUT_SECS=30 \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

Result after the renderer change:

- `electron_simple_web_layout_status=pass`
- `electron_simple_web_layout_reason=pass`
- `electron_simple_web_layout_mismatch_count=0`
- `electron_simple_web_layout_text_color_delta_pixels=0`
- `electron_simple_web_layout_surface_geometry_pixels=0`
- `electron_simple_web_layout_blur_or_tolerance_used=false`

Previous production evidence for the same case:

- `electron_simple_web_layout_mismatch_count=50`
- `electron_simple_web_layout_text_color_delta_pixels=50`
- `electron_simple_web_layout_surface_geometry_pixels=0`

The change reduces the smallest exact layout mismatch from 50 to 18 pixels. It
The refined threshold phase then reduces the same case from 18 mismatches to an
exact pass without blur/tolerance.

## Broader Probe

Additional probes remained divergent but improved:

- `border_nested_matrix`: 1105 -> 779 mismatches.
- `position_z_index_matrix`: 1833 -> 1708 mismatches.

Both still report `surface_geometry_pixels=0`, so the remaining blocker is
gradient/color quantization, not layout geometry.

## Tests

- `bin/simple check src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl`
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --mode=interpreter --clean`
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl --mode=interpreter --clean`
- `bin/simple spipe-docgen test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_spec.spl --output doc/06_spec --no-index`

## Remaining Work

`css_box_matrix` now reaches exact parity. Full production GUI/web parity
remains incomplete until the other exact layout cases also reach
`mismatch_count=0` or the manifest explicitly records narrower tracked
Chromium-dither policies with release gates that still forbid blur/tolerance.
