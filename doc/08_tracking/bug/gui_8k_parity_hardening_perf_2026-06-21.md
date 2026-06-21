# GUI 8K Parity Hardening Perf Blocker

Date: 2026-06-21

## Summary

The 8K packed-surface evidence wrapper passes, but its maintained system spec
is slow enough for the runner to flag it as a perf bug.

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

## Required Fix

Keep the 8K packed-surface assertions, but split or optimize the renderer parity
system spec so the focused 8K evidence wrapper no longer depends on a slow full
renderer-parity run for every check.
