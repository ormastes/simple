# GUI 8K Parity Hardening Perf Blocker

Date: 2026-06-21
Status: Resolved 2026-06-21

## Summary

The 8K packed-surface evidence wrapper originally passed through the full
renderer parity hardening spec, which was slow enough for the runner to flag it
as a perf bug. The wrapper now uses a focused 8K surface-planning spec for the
packed-surface assertions and leaves the broader renderer spec for backend
parity coverage.

## Evidence

Command:

```bash
SIMPLE_BIN=src/compiler_rust/target/debug/simple \
  sh scripts/check/check-gui-color-image-pipeline-8k-evidence.shs
```

Result:

- `gui_color_image_pipeline_8k_status=pass`
- `test/03_system/gui/wm_compare/production_gui_web_renderer_parity_hardening_spec.spl`
  passed 10 scenarios in about 65 seconds and was marked `[PERF BUG]`
- `test/01_unit/lib/common/color/color_lab_xyz_spec.spl` passed 4 scenarios

## Resolution

- Added `test/03_system/gui/wm_compare/production_gui_8k_surface_planning_spec.spl`
  with the exact 8K packed framebuffer, lazy-init, and format eligibility
  assertions.
- Regenerated
  `doc/06_spec/test/03_system/gui/wm_compare/production_gui_8k_surface_planning_spec.md`.
- Updated `scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` to run
  the focused 8K planning spec instead of the full renderer parity hardening
  spec.
- Latest wrapper evidence passes with the 8K planning spec at about 5 seconds
  and no `[PERF BUG]` marker in the focused evidence report.

## Remaining Image-Decode Follow-Up

The resolved perf blocker covers 8K packed-surface planning and lazy startup.
It does not complete full JPEG XL pixel decode. Current 8K evidence covers
TIFF raster paths, JPEG XL metadata parsing, sparse 8K placeholder allocation,
structured default-sRGB metadata, non-default color fail-closed routing, and
exact raster tiling. Do not mark image URI rendering complete until the asset
resolver feeds real PNG/JPEG/WebP/TIFF/JPEG XL pixels into Engine2D and full
JPEG XL pixel decode has its own SPipe evidence.
