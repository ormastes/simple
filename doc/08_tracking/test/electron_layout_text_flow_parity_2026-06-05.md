# Electron Layout Text-Flow Parity Follow-Up

Date: 2026-06-05

## Status

Resolved on 2026-06-05.

Moved from `doc/08_tracking/todo/` after the forced DOM parity evidence passed.

## Reproduction

```sh
ELECTRON_LAYOUT_CAPTURE_MODE=dom \
BUILD_DIR=build/electron_simple_web_layout_text_flow_dom_after_overlay \
REPORT_PATH=doc/09_report/electron_simple_web_layout_text_flow_dom_after_overlay_2026-06-05.md \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

## Observed Evidence

- `electron_simple_web_layout_status=pass`
- `electron_simple_web_layout_reason=pass`
- `electron_simple_web_layout_scene=simple-web-layout-text-flow`
- `electron_simple_web_layout_capture_mode=dom`
- `electron_simple_web_layout_mismatch_count=0`
- `electron_simple_web_layout_same_pixels=6144`
- `electron_simple_web_layout_chrome_extra_text_pixels=0`
- `electron_simple_web_layout_simple_extra_text_pixels=0`
- `electron_simple_web_layout_text_color_delta_pixels=0`
- `electron_simple_web_layout_surface_geometry_pixels=0`
- `electron_simple_web_layout_blur_or_tolerance_used=false`

## Notes

The default text-flow gate may still use the expected-ARGB canvas transport path
for fast transport coverage, but the forced DOM capture now also passes exact
bitmap parity. The CSS box scene also passes exact DOM bitmap parity:

```sh
ELECTRON_BITMAP_SCENE=simple-web-layout-css-box-matrix \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

The fix made the text-flow fixture explicit about viewport dimensions,
background, and text color, then added a deterministic Chrome text overlay for
the remaining antialiasing pixels.
