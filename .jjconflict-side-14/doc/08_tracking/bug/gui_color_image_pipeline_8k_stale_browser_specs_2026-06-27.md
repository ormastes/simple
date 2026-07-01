# GUI Color/Image Pipeline 8K Stale Browser Specs

Date: 2026-06-27

## Summary

`scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` referenced
focused browser specs and generated-probe imports that are absent in the current
tree. With the self-hosted Simple binary, the wrapper can no longer produce a
valid normal 8K GUI color/image evidence row from those stale paths.

Status: resolved by replacing the stale browser-example dependencies with a
current core-module probe over `std.common.color.lab_xyz` and
`std.common.image.image_info`.

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
