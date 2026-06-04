# CUDA Engine2D Mirror-Only Readback Gap - 2026-05-29

## Status

Resolved for the documented core primitives. `draw_line`, `draw_circle`,
`draw_circle_filled`, `draw_rounded_rect`, and `draw_triangle_filled` now have
CUDA PTX kernels or verified mirror-to-device synchronization. `draw_text`,
clip, and mask behavior have strict device-readback coverage.

## Problem

`CudaBackend` implements the same `RenderBackend` interface as CPU and Metal,
but several primitives still draw only into the software mirror. When CUDA is
initialized, `read_pixels()` prefers device framebuffer readback, so a sequence
such as `clear()` followed by a mirror-only primitive can return stale device
pixels instead of the mirror result.

Previously confirmed mirror-only core primitives:

- `draw_text`
- clip and mask state

Extended operations remain outside this core bug unless a separate strict
readback parity gap is found.

## Attempted Fix

A fallback that copied the full software mirror back to the CUDA framebuffer
after `draw_line` was rejected during verification. It destabilized
`test/02_integration/rendering/cuda_strict_spec.spl`, leaving the strict suite at
15 passed / 1 failed on this host even after the added `draw_line` assertion was
removed.

## Completed Fix

Added real CUDA primitive coverage for `kernel_draw_line`, `kernel_draw_circle`,
`kernel_draw_circle_filled`, `kernel_draw_rounded_rect`, and
`kernel_draw_triangle_filled` instead of silently relying on mirror-only state
while device readback remains preferred.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl test/02_integration/rendering/cuda_strict_spec.spl test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/02_integration/rendering/cuda_strict_spec.spl --mode=interpreter --clean`
  - Result: 21 passed, 0 failed.
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl --mode=interpreter --clean`
  - Result: 8 passed, 0 failed.

## Re-verification (2026-05-29)

The previously listed `draw_text`, clip, and mask readback gaps are covered by
`test/02_integration/rendering/cuda_strict_spec.spl` and pass on this host.

Verification:

- `SIMPLE_LIB=src bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl test/02_integration/rendering/cuda_strict_spec.spl test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl --mode=interpreter --clean`
  - Result: 8 passed, 0 failed.
- `SIMPLE_LIB=src bin/simple test test/02_integration/rendering/cuda_strict_spec.spl --mode=interpreter --clean`
  - Result: 25 passed, 0 failed.
