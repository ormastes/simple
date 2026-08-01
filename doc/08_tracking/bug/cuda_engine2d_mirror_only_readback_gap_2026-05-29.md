# CUDA Engine2D Mirror-Only Readback Gap - 2026-05-29

Status: Resolved for the documented core primitives. `draw_line`, `draw_circle`,

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

## Processing-Lane Probe Hardening (2026-06-11)

Closed the processing-lane probe gap (AC-1). Changes:

- `probe_cuda_2d()`: `feature_gate` renamed from `"cuda_device"` to `"cuda-device-unavailable"`
  when `cuda_device_count() < 1`, so callers have a structured evidence string rather
  than a generic identifier.
- `probe_cuda_processing()` added as an explicit processing-lane entry point that
  delegates to `probe_cuda_2d()` — mirrors the ROCm `probe_rocm()` pattern.

Verified on this host (no NVIDIA GPU, nvcc 13.0 present):

- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.spl`
  - Result: 7 passed, 0 failed (interpreter mode).
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl --clean`
  - Result: 9 passed, 2 failed (2 failures are pre-existing, unrelated to probe changes).

The 2 pre-existing failures in the renderbackend spec were present before this
change and are not caused by it (confirmed by reverting and re-running). They
should be investigated separately.

## P6 Readback Spec Gap Closure (2026-06-12)

Closed the 2 pre-existing spec failures identified in the 2026-06-11 note:

1. `draw_text_bg` method not found on `CudaBackend` — the implementation lives
   in `backend_cuda_ext.spl` as `impl Engine2DExtended for CudaBackend`, but
   the spec did not import that module. Fix: added
   `use std.gpu.engine2d.backend_cuda_ext` to
   `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`.

2. `is_usable()` method not found on `BackendProbeResult` — `BackendProbe3D`
   had this method but the 2D `BackendProbeResult` did not. Fix: added
   `fn is_usable() -> bool: self.status == BackendStatus.Initialized` to
   `BackendProbeResult` in `backend_probe.spl`, matching the 3D pattern.

The device→host readback path itself (`cuda_memcpy_dtoh` in `read_pixels()`)
was already implemented and correct; the gap was purely in spec coverage — the
tests that should have verified it were failing to compile, not failing at
runtime. No new `rt_cuda_*` externs required; no seed rebuild needed.

Verified on this host (no NVIDIA GPU, nvcc 13.0 present):

- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_renderbackend_spec.spl`
  - Before: 9 passed, 2 failed.
  - After: 11 passed, 0 failed.
- `bin/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_cuda_processing_spec.spl`
  - Result: 7 passed, 0 failed (unchanged).
