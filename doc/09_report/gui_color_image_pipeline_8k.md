# GUI Color/Image Pipeline 8K Report

Date: 2026-06-01

Canonical lane report for `gui_color_image_pipeline_8k`.

Current evidence is produced by:

```sh
sh scripts/check-gui-color-image-pipeline-8k-evidence.shs
```

The dated reports under `doc/09_report/gui_color_image_pipeline_8k_evidence_*.md` are the execution records. The gate covers packed 8K framebuffer planning, lazy Lab/XYZ/TIFF/JPEG XL startup state, exact TIFF RGBA slices, staged JPEG XL metadata and sparse 8K allocation, and ICC profile routing. As of 2026-06-01, RGB/Lab ICC profiles fail closed with `icc-rgb-lab-transform-pending` rather than being accepted as identity pixels.
