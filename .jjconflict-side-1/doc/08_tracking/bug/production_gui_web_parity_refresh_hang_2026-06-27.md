# Production GUI/Web Parity Refresh Hang

- Date: 2026-06-27
- Status: mitigated; paint/text parity still open
- Area: production GUI/web renderer parity evidence
- Command: `sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs`

## Symptom

The production GUI/web parity evidence refresh produced no stdout for more than
two minutes and required manual termination to avoid an unbounded agent session.

The process tree showed the refresh inside the Electron Simple Web layout
manifest wrapper, currently running the `position_z_index_matrix` case:

```text
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
timeout 180 env ... sh scripts/check/check-electron-simple-web-layout-manifest-evidence.shs
sh scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs
release/x86_64-unknown-linux-gnu/simple run .../position_z_index_matrix/simple_web_layout_expected.spl --mode=interpreter --clean
```

The refresh process groups were terminated with `TERM` after Ctrl-C did not stop
the session promptly.

## Evidence

Partial case evidence was still written under:

`build/production_gui_web_renderer_parity_evidence/layout_manifest/position_z_index_matrix/`

The case classified as divergent with matching surface geometry but text raster
differences:

```text
electron_simple_web_layout_status=divergent
electron_simple_web_layout_reason=checksum-mismatch
electron_simple_web_layout_mismatch_count=1708
electron_simple_web_layout_chrome_extra_text_pixels=34
electron_simple_web_layout_simple_extra_text_pixels=0
electron_simple_web_layout_text_color_delta_pixels=1674
electron_simple_web_layout_surface_geometry_pixels=0
electron_simple_web_layout_simple_bin=release/x86_64-unknown-linux-gnu/simple
electron_simple_web_layout_simple_bin_source=repo-self-hosted-fallback
electron_simple_web_layout_simple_bin_status=pass
```

## Impact

The production parity gate can look like a layout/z-index failure even when box
geometry matches. The refresh path can also consume agent wall time without
visible progress if a per-case Simple run stalls.

## Follow-Up

- Done: the wrapper remains fail-closed.
- Done: residual mismatch classes distinguish text raster mismatches from
  surface geometry mismatches.
- Done: the Simple expected-frame run is bounded by
  `ELECTRON_BITMAP_TIMEOUT_SECS` and emits `electron_simple_web_layout_simple_expected_*`
  rows on timeout or failure.
- Open: fix the underlying Electron/Simple paint or text raster divergence. The
  text-free `position_z_index_matrix` case should classify residual color-only
  differences as `paint-color-mismatch`, not text glyph raster drift.

## 2026-06-27 Gradient Quantization Attempt

Bounded follow-up on `simple-web-layout-position-z-index-matrix` confirmed the
residual failure is still paint-only:

```text
electron_simple_web_layout_status=divergent
electron_simple_web_layout_reason=paint-color-mismatch
electron_simple_web_layout_mismatch_count=1708
electron_simple_web_layout_same_pixels=4436
electron_simple_web_layout_surface_geometry_pixels=0
electron_simple_web_layout_simple_expected_timed_out=false
```

Two renderer experiments were rejected and reverted:

- Per-pixel default-gradient quantization matched the likely Chrome sampling
  direction but made the expected-frame path exceed
  `ELECTRON_BITMAP_TIMEOUT_SECS=20`, reproducing the resource/crash risk.
- Row-batched center sampling avoided the timeout but worsened this fixture to
  `electron_simple_web_layout_mismatch_count=1761`.

Keep the current endpoint-exact row path until a Chrome-derived gradient oracle
or faster mutable framebuffer pixel writer is available. Do not reintroduce the
per-pixel repeated-gradient loop through `fb_rounded_rect_corners_opacity_clip`;
it is too slow in the self-hosted interpreter evidence path.
