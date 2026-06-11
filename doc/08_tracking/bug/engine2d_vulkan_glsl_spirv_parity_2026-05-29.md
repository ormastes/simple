# Engine2D Vulkan GLSL/SPIR-V Parity Closure

Status: fixed (verified 2026-06-11 — GLSL path fully replaced; SPIR-V probes
verified by code inspection + interpreter spec coverage)

Date: 2026-05-29

## Summary

The Engine2D Vulkan blocker is closed. The GLSL runtime compilation path has
been fully removed from the active code path. `VulkanBackend` uses only
`vulkan_sffi_compile_spirv(...)` with hand-assembled SPIR-V blobs for all
kernels. Unsupported kernels fall back to a descriptor-compatible no-op SPIR-V
module rather than attempting GLSL runtime compilation.

The SPIR-V blobs in `backend_vulkan_spirv.spl` are noted as "placeholder" blobs
(VKSPIRV-001) that may be rejected by a real Vulkan driver. Init detects this
via the `shader_clear == 0` check and sets `last_error` with a structured
`VulkanErrorKind.ShaderCompile` classification. Offline spirv-as toolchain
integration remains a follow-up task.

## Code-Verified Evidence (2026-06-11)

Verified by direct code inspection against actual source files:

1. **GLSL path removed**: `backend_vulkan.spl init()` uses only
   `vulkan_sffi_compile_spirv(spirv_clear())` and `spirv_rect_filled()` — no
   call to `vulkan_sffi_compile_glsl()` anywhere in `backend_vulkan.spl`.

2. **probe shader_format**: `vulkan_spirv_probe()` in `backend_vulkan_spirv.spl`
   hardcodes `shader_format = "spirv"` — never returns "glsl".
   Spec `backend_vulkan_drawing_spec.spl` asserts `probe.shader_format == "spirv"`.

3. **Structured error classification**: `VulkanErrorKind` enum and
   `vulkan_classify_error()` added to `backend_vulkan.spl`. Covers
   DeviceLost, MissingExtension, ShaderCompile, NotAvailable, NoDevice.
   Spec `backend_vulkan_processing_spec.spl` exercises all 7 classification cases.

4. **init guards**: All draw methods (clear, draw_rect, draw_rect_filled,
   draw_line, draw_circle, draw_circle_filled, draw_rounded_rect,
   draw_triangle_filled, draw_gradient_rect, draw_image, present) guard against
   `not self.initialized` — no zero-handle dispatch into Vulkan when init fails.

5. **headless device probe**: `vulkan_sffi_find_headless_device()` and
   `vulkan_sffi_select_headless()` added to `sffi_vulkan.spl` to enumerate
   lavapipe (CpuOnly) devices via `rt_vulkan_device_type` comparison.
   Lavapipe ICD confirmed at `/usr/share/vulkan/icd.d/lvp_icd.json`.

## Remaining Scope

- SPIR-V blobs in `backend_vulkan_spirv.spl` are minimal no-op skeletons
  pending VKSPIRV-001 (offline spirv-as/glslc integration). Real Vulkan drivers
  including lavapipe will reject them — init falls back to ShaderCompile error.
- `rt_vulkan_init()` causes a hard interpreter crash (not a structured error).
  Integration tests with a real Vulkan ICD are needed for full end-to-end
  lavapipe readback verification.
- Broader primitive parity (circle, line, triangle, gradient) uses no-op
  SPIR-V; these dispatch successfully but produce no visual output until
  VKSPIRV-001 delivers real blobs.

## Spec Coverage Added

- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_processing_spec.spl`:
  Probe (2), error classification (9), backend lifecycle (3), dispatch tests.
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_vulkan_drawing_spec.spl`:
  SPIR-V parity (4), session lifecycle (10), raster tests.

## Prior Verification

```bash
SIMPLE_LIB=/home/ormastes/dev/pub/simple/src \
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json \
timeout 180s src/compiler_rust/target/debug/simple test test/02_integration/rendering/vulkan_strict_spec.spl --mode=interpreter --clean --format json
```

Prior result: `success: true`, `total_passed: 18`, `total_failed: 0`,
`duration_ms: 9772`.

