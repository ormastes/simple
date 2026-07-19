# GPU font atlas / composite path accepts invalid inputs and mis-aligns readback

**Date:** 2026-07-17
**Status:** fixed / landed (SHAs below)
**Severity:** P2 — invalid atlas subrects and unguarded WGSL composite inputs
produce corrupt glyph composites / readback; distinct from the earlier
"readback missing" gap.
**Component:** GPU font atlas composite path — `src/lib/common/gpu/font_atlas_composite.spl`,
`src/compiler/70.backend/backend/gpu_portable_compute.spl`, Engine2D Vulkan/CUDA
font backends.

## Symptom

The GPU font atlas / composite path did not validate its inputs:

- invalid atlas subrects (out-of-bounds / degenerate rectangles) were accepted
  and composited, producing garbage glyph regions;
- WGSL composite inputs were unguarded;
- GPU composite readback was mis-aligned;
- emitted font source bytes were not bound to the composite invocation.

## Root cause

Missing bounds/validity checks on atlas subrects and WGSL composite inputs, a
readback alignment mismatch, and an unbound font-source-bytes input in the
portable-compute font composite path. These are input-validation / binding
defects in the GPU font atlas pipeline — separate from
`production_gui_font_offload_runtime_readback_2026-06-23.md`, which was about the
glyph readback being *absent* rather than mis-validated/mis-aligned.

## Fixing commits

- `be3ac62df6c` fix(fonts): reject invalid atlas subrects
- `b694e04936d` fix(fonts): guard WGSL composite inputs
- `6f47f385d7f` fix(fonts): align GPU composite readback
- `bf1de3d7faa` fix(gpu): bind emitted font source bytes

## Affected files

- `src/lib/common/gpu/font_atlas_composite.spl`
- `src/compiler/70.backend/backend/gpu_portable_compute.spl`
- `src/app/portable_compute_emit/main.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_font_spirv.spl`
- `src/lib/gc_async_mut/gpu/engine2d/backend_cuda_font_ptx.spl`
- `src/lib/gc_async_mut/gpu/engine2d/engine.spl`

## Related

- `production_gui_font_offload_runtime_readback_2026-06-23.md` — earlier,
  distinct GPU font-offload bug (glyph readback missing entirely).
- `cuda_font_companion_package_trust_anchor_2026-07-15.md` — CUDA font companion
  trust anchor (separately tracked).
