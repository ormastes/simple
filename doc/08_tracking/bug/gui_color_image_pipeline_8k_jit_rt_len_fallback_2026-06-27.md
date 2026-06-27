# GUI Color/Image 8K JIT rt_len Fallback

Date: 2026-06-27

## Summary

`scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` now passes with
the self-hosted Simple binary, but the generated current-source probe first
logs:

```text
Cranelift JIT compile: Module error: unresolved external symbol 'rt_len' would NULL-jump in JIT; deferring to interpreter
```

The interpreter fallback still emits a valid evidence row, but this is not the
desired optimized native/JIT path for the GUI 8K lane.

## Evidence

The passing row includes:

- `gui_color_image_pipeline_8k_status=pass`
- `gui_color_image_pipeline_8k_reason=pass`
- `gui_color_image_pipeline_8k_simple_bin_status=pass`
- `gui_color_image_pipeline_8k_framebuffer_bytes=132710400`
- `gui_color_image_pipeline_8k_image_fail_closed_ok=true`

## Required Fix

Fix the self-hosted JIT/native symbol lowering or linkage for string/list
length operations so this probe does not need interpreter fallback. Keep the
existing pass row as correctness evidence only; do not use it as proof that the
8K color/image evidence probe is running on the optimized native/JIT path.
