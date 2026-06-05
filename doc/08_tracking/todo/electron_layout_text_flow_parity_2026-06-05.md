# Electron Layout Text-Flow Parity Follow-Up

Date: 2026-06-05

## Status

Open.

## Reproduction

```sh
ELECTRON_LAYOUT_CAPTURE_MODE=dom \
BUILD_DIR=build/electron_simple_web_layout_text_flow_fresh \
REPORT_PATH=doc/09_report/electron_simple_web_layout_text_flow_fresh_2026-06-05.md \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

## Observed Evidence

- `electron_simple_web_layout_status=divergent`
- `electron_simple_web_layout_reason=checksum-mismatch`
- `electron_simple_web_layout_scene=simple-web-layout-text-flow`
- `electron_simple_web_layout_mismatch_count=6144`
- `electron_simple_web_layout_same_pixels=0`
- `electron_simple_web_layout_chrome_extra_text_pixels=6065`
- `electron_simple_web_layout_text_color_delta_pixels=79`
- `electron_simple_web_layout_surface_geometry_pixels=0`
- `electron_simple_web_layout_blur_or_tolerance_used=false`

## Notes

The default text-flow gate intentionally uses the expected-ARGB canvas transport
path so Electron live capture/readback remains exact while DOM text parity is
tracked separately by the command above. The CSS box scene also passes exact DOM
bitmap parity:

```sh
ELECTRON_BITMAP_SCENE=simple-web-layout-css-box-matrix \
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
```

This isolates the current gap to text-flow/text-raster parity rather than the
evidence artifact write path or Electron capture plumbing.
