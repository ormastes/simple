# Feature Request: Engine2D Facade Must Preserve Backend Pixel Mutations

Date: 2026-06-02
Status: open
Area: Engine2D, render backends, web renderer parity

## Problem

Backend-executed parity evidence found that direct concrete backends preserve
drawn pixels, but the generic `Engine2D` facade path can lose pixel mutations
when drawing through the `RenderBackend` trait field.

The reduced scene:

- clear `0xFF102030`
- filled rect `0xFF010204`

passes exact parity when driven directly through:

- `SoftwareBackend`
- `CpuBackend`
- `MetalBackend`

The same scene driven through `Engine2D.create_with_backend(...).backend`
returned opaque black for software and CPU SIMD pixels while Metal direct
readback returned the expected colors.

## Expected Behavior

`Engine2D` should be the canonical production facade. Drawing through
`Engine2D.clear`, `Engine2D.draw_rect_filled`, `Engine2D.present`, and
`Engine2D.read_pixels` must produce the same pixels as the concrete backend.

## Required Fix

Refactor `Engine2D` so backend state mutations cannot be lost behind trait-field
dispatch. Acceptable approaches:

- Store concrete backend variants explicitly and dispatch through typed fields.
- Introduce a boxed/reference backend model with proven mutation semantics.
- Add a generated backend enum wrapper if that matches Simple language limits.

## Acceptance Criteria

- A spec proves `Engine2D.create_with_backend(16, 16, "software")` preserves
  clear and filled-rect colors.
- A spec proves `Engine2D.create_with_backend(16, 16, "cpu_simd")` preserves
  the same colors and records SIMD hits.
- On macOS, a spec proves `Engine2D.create_with_backend(16, 16, "metal")`
  returns exact pixels from GPU readback for the reduced scene.
- The web renderer backend parity harness can use `Engine2D` directly without
  falling back to direct concrete backend calls.

## Notes

This is not a request to hardcode web-rendered pixels. The final renderer path
must remain HTML/CSS-driven and backend-selectable.

## Current Evidence - 2026-07-02

Partial evidence now exists, and the local software/CPU SIMD facade acceptance
criteria are now covered by executable unit evidence:

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.spl`
  proves `Engine2D.create_with_backend(16, 16, "software")` preserves clear and
  filled-rect colors through `Engine2D.clear`, `Engine2D.draw_rect_filled`,
  `Engine2D.present`, and `Engine2D.read_pixels`.
- The same spec proves the public software facade path honors `Engine2D.set_clip`
  and `Engine2D.set_mask` for `Engine2D.draw_image`, so the optimized software
  blit path cannot bypass clip/mask state.
- The same spec proves `Engine2D.create_with_backend(16, 16, "cpu_simd")`
  preserves the same colors and records SIMD fill hits through the facade path.
- The same spec proves the public CPU SIMD facade path also honors
  `Engine2D.set_clip` and `Engine2D.set_mask` for `Engine2D.draw_image`.
- The same spec proves software and CPU SIMD facade paths also preserve
  clip/mask state for `Engine2D.draw_image_scaled`, which routes through the
  shared `draw_image` backend contract.
- The same spec proves software and CPU SIMD facade paths also preserve
  clip/mask state for `Engine2D.draw_image_transform`, which routes through the
  shared transformed-image emulator and backend `draw_image` contract.
- `doc/06_spec/test/01_unit/lib/gc_async_mut/gpu/engine2d/engine2d_facade_backend_mutation_spec.md`
  is the generated manual for the focused facade evidence.
- `doc/09_report/cpu_simd_engine2d_evidence_current_2026-07-02.md` proves the
  current x86_64 CPU SIMD Engine2D path executes native AVX2 kernels and matches
  scalar pixels with zero mismatches for fill/copy/alpha/scroll/diagram cases.
- `doc/09_report/vulkan_engine2d_readback_2026-07-02.md` proves the current
  Vulkan Engine2D path exercises present/readback and matches clear/rect pixel
  oracles with zero mismatches.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/vulkan_compute_oracle_spec.spl`
  now proves `VulkanBackend.draw_image` uploads source pixels into the Vulkan
  framebuffer, handles clipped and masked source pixels, and reads them back
  through the device path.
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_backend_parity_spec.spl`
  proves the Simple web renderer Engine2D-backed parity harness matches
  software pixels for CPU, CPU SIMD, Metal-on-Vulkan, CUDA fallback, OpenCL
  fallback, and Vulkan on the generic layout fixture.
- `doc/09_report/linux_renderdoc_simpleos_hardening_evidence_current_2026-07-02.md`
  is the combined current evidence index for Linux RenderDoc/Vulkan, Engine2D,
  CPU SIMD, QEMU access, SimpleOS hardening, and LLVM-to-SimpleOS status.

Still required before closing this feature: macOS Metal exact-readback evidence
when available.
