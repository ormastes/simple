# GUI Color/Image 8K JIT rt_len Fallback

Date: 2026-06-27

## Summary

Resolved for the 8K interpreter evidence wrapper. The wrapper now sets
`SIMPLE_EXECUTION_MODE=interpret` around its generated evidence run and focused
spec run, so the self-hosted binary no longer tries the outer Rust-driver JIT
before honoring the interpreter evidence path.

Before the fix, `scripts/check/check-gui-color-image-pipeline-8k-evidence.shs`
passed with the self-hosted Simple binary, but the generated current-source
probe first logged:

```text
Cranelift JIT compile: Module error: unresolved external symbol 'rt_len' would NULL-jump in JIT; deferring to interpreter
```

That fallback was misleading for an explicitly interpreter-mode evidence gate.
It is no longer emitted by the wrapper.

## Evidence

The passing row now includes:

- `gui_color_image_pipeline_8k_status=pass`
- `gui_color_image_pipeline_8k_reason=pass`
- `gui_color_image_pipeline_8k_simple_bin_status=pass`
- `gui_color_image_pipeline_8k_simple_execution_mode=interpret`
- `gui_color_image_pipeline_8k_framebuffer_bytes=132710400`
- `gui_color_image_pipeline_8k_image_fail_closed_ok=true`

Focused rerun evidence:

- wrapper exit code: `0`
- `jit_fallback=absent`

## Remaining Native/JIT Work

This resolves the wrapper contract only. It is not proof that the 8K
color/image evidence probe is running on the optimized native/JIT path. A
separate compiler/codegen lane still needs focused proof before claiming
generic string/list length lowering is fully JIT/native-clean.
