# GUI Color/Image Pipeline 8K Report

Date: 2026-06-01

Canonical lane report for `gui_color_image_pipeline_8k`.

Current evidence is produced by:

```sh
sh scripts/check/check-gui-color-image-pipeline-8k-evidence.shs
```

The dated reports under `doc/09_report/gui_color_image_pipeline_8k_evidence_*.md` are the execution records. The gate covers packed 8K framebuffer planning, lazy Lab/XYZ/TIFF/JPEG XL startup state, exact TIFF RGBA slices, staged JPEG XL metadata and sparse 8K allocation, and ICC profile routing. As of 2026-06-01, RGB/Lab ICC profiles fail closed with `icc-rgb-lab-transform-pending` rather than being accepted as identity pixels.

Current evidence must also include self-hosted Simple binary provenance:
`gui_color_image_pipeline_8k_simple_bin`,
`gui_color_image_pipeline_8k_simple_bin_source`, and
`gui_color_image_pipeline_8k_simple_bin_status=pass`. Any
`src/compiler_rust/**` override fails before the generated 8K probe or focused
specs run with `gui_color_image_pipeline_8k_reason=simple-bin-forbidden`; that
is blocked evidence, not a valid 8K GUI pipeline pass.

As of 2026-06-27, the wrapper also fails explicitly with
`gui_color_image_pipeline_8k_reason=missing-focused-spec` when the focused
browser specs referenced by the old lane are absent. Track that blocker in
`doc/08_tracking/bug/gui_color_image_pipeline_8k_stale_browser_specs_2026-06-27.md`.
