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
`gui_color_image_pipeline_8k_simple_bin_status=pass`. Interpreter evidence must
also record `gui_color_image_pipeline_8k_simple_execution_mode=interpret` and
must not emit the previous `rt_len` JIT fallback log. Any
`src/compiler_rust/**` override fails before the generated 8K probe or focused
specs run with `gui_color_image_pipeline_8k_reason=simple-bin-forbidden`; that
is blocked evidence, not a valid 8K GUI pipeline pass.

As of 2026-06-27, the wrapper no longer depends on the removed
`examples/11_advanced/browser/**` focused specs. The generated probe uses the
current `std.common.color.lab_xyz` and `std.common.image.image_info` modules and
must emit `gui_color_image_pipeline_8k_image_fail_closed_ok=true` before the
row counts as a current-source pass. Historical stale-spec details are recorded
in `doc/08_tracking/bug/gui_color_image_pipeline_8k_stale_browser_specs_2026-06-27.md`.
