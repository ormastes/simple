# GUI Color/Image Pipeline 8K Stale Browser Specs

## Closed 2026-09-13 — stale browser-example deps replaced by a core-module probe, as recorded
- **measured**: `grep -cE 'lab_xyz|image_info' scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` = 12 — the `std.common.color.lab_xyz` / `std.common.image.image_info` probe named in the resolution is wired in.
- **measured**: the three stale paths this entry named under `examples/11_advanced/browser/test/` do not exist — consistent with removal as dependencies rather than restoration.
- **inferred**: the wrapper itself was not executed (Linux GPU 8K evidence lane, unavailable on this Windows host).

Date: 2026-06-27

## Summary

`scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` referenced
focused browser specs and generated-probe imports that are absent in the current
tree. With the self-hosted Simple binary, the wrapper can no longer produce a
valid normal 8K GUI color/image evidence row from those stale paths.

**Status:** CLOSED 2026-09-13 (see Closed section above)

## Previous Evidence

Before the fix, the wrapper failed explicitly before the generated probe with:

- `gui_color_image_pipeline_8k_status=fail`
- `gui_color_image_pipeline_8k_reason=missing-focused-spec`
- `gui_color_image_pipeline_8k_missing_focused_specs=...`
- `gui_color_image_pipeline_8k_simple_bin_status=pass`

This replaces the prior ambiguous failure where the generated probe tried to
import `examples.browser.feature.gpu.surface` and the self-hosted resolver could
not find the module.

## Missing Paths

- `examples/11_advanced/browser/test/gpu/surface_color_plan_spec.spl`
- `examples/11_advanced/browser/test/paint/image_decode_spec.spl`
- `examples/11_advanced/browser/test/gpu/tiff_image_raster_spec.spl`

## Required Fix

Completed in the same lane: the generated probe imports current module paths and
normal wrapper evidence now requires:

- `gui_color_image_pipeline_8k_status=pass`
- `gui_color_image_pipeline_8k_reason=pass`
- `gui_color_image_pipeline_8k_simple_bin_status=pass`
- `gui_color_image_pipeline_8k_image_fail_closed_ok=true`
