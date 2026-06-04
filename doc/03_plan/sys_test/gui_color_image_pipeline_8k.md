# GUI Color/Image Pipeline 8K System Test Plan

Date: 2026-06-01

## Gate

Run:

```sh
BUILD_DIR=build/gui_color_image_pipeline_8k_evidence \
REPORT_PATH=doc/09_report/gui_color_image_pipeline_8k_evidence_2026-06-01.md \
sh scripts/check/check-gui-color-image-pipeline-8k-evidence.shs
```

## Coverage

- Generated 8K probe: packed BGRA8 dimensions, byte counts, lazy init flags, CIELAB semantic space, CIE XYZ connection space, RGB565 packed-path rejection, and Lab/XYZ/packed ARGB roundtrip.
- `examples/11_advanced/browser/test/gpu/surface_color_plan_spec.spl`: browser surface policy.
- `test/01_unit/lib/common/color/color_lab_xyz_spec.spl`: color conversion and surface planning helpers.
- `examples/11_advanced/browser/test/paint/image_decode_spec.spl`: browser decode metadata, sparse 8K placeholders, JPEG XL staged metadata, ICC routing, and fail-closed profile diagnostics.
- `examples/11_advanced/browser/test/gpu/tiff_image_raster_spec.spl`: TIFF raster evidence through browser/GPU-facing rasterization.

## Pass Criteria

The script must exit zero, report `gui_color_image_pipeline_8k_status=pass`, and write a report under `doc/09_report/`. Any failed focused spec, non-exact TIFF raster assertion, eager initialization flag, unsupported-path false pass, or missing 8K byte-count evidence fails the lane.
