# CUDA Engine2D Mirror-Only Readback Gap - 2026-05-29

## Status

Partially resolved. `draw_line`, `draw_circle`, `draw_circle_filled`,
`draw_rounded_rect`, and `draw_triangle_filled` now have CUDA PTX kernels and
strict readback coverage. Other mirror-only primitives remain open.

## Problem

`CudaBackend` implements the same `RenderBackend` interface as CPU and Metal,
but several primitives still draw only into the software mirror. When CUDA is
initialized, `read_pixels()` prefers device framebuffer readback, so a sequence
such as `clear()` followed by a mirror-only primitive can return stale device
pixels instead of the mirror result.

Confirmed remaining mirror-only core primitives:

- `draw_text`
- clip and mask state

Extended operations are also mirror-only unless explicitly implemented in the
CUDA backend.

## Attempted Fix

A fallback that copied the full software mirror back to the CUDA framebuffer
after `draw_line` was rejected during verification. It destabilized
`test/integration/rendering/cuda_strict_spec.spl`, leaving the strict suite at
15 passed / 1 failed on this host even after the added `draw_line` assertion was
removed.

## Completed Fix

Added real CUDA primitive coverage for `kernel_draw_line`, `kernel_draw_circle`,
`kernel_draw_circle_filled`, `kernel_draw_rounded_rect`, and
`kernel_draw_triangle_filled` instead of silently relying on mirror-only state
while device readback remains preferred.

Verification:

- `bin/simple check src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl test/integration/rendering/cuda_strict_spec.spl test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`
- `SIMPLE_LIB=src bin/simple test test/integration/rendering/cuda_strict_spec.spl --mode=interpreter --clean`
  - Result: 21 passed, 0 failed.
- `SIMPLE_LIB=src bin/simple test test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl --mode=interpreter --clean`
  - Result: 8 passed, 0 failed.

## Remaining Fixes

Target files:

- `src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl`
- `test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`
- `test/integration/rendering/cuda_strict_spec.spl`

The next strict hardware tests should compare CUDA text, clip, and mask behavior
against the CPU reference after `clear()`.
