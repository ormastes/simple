# CUDA Engine2D Mirror-Only Readback Gap - 2026-05-29

## Status

Open.

## Problem

`CudaBackend` implements the same `RenderBackend` interface as CPU and Metal,
but several primitives still draw only into the software mirror. When CUDA is
initialized, `read_pixels()` prefers device framebuffer readback, so a sequence
such as `clear()` followed by a mirror-only primitive can return stale device
pixels instead of the mirror result.

Confirmed mirror-only core primitives:

- `draw_line`
- `draw_circle`
- `draw_circle_filled`
- `draw_rounded_rect`
- `draw_triangle_filled`
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

## Required Fix

Add real CUDA primitive coverage, starting with `kernel_draw_line`, instead of
silently relying on mirror-only state while device readback remains preferred.

Target files:

- `src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl`
- `test/unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`
- `test/integration/rendering/cuda_strict_spec.spl`

The strict hardware test should compare CUDA `draw_line` pixels against the CPU
reference after `clear()`.
