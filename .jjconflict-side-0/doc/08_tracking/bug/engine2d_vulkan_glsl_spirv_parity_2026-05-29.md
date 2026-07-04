# Engine2D Vulkan GLSL/SPIR-V Parity Closure

Status: fully closed (2026-06-12 — VKSPIRV-001 resolved; rt_vulkan_init crash
confirmed not reproducible; all 10 kernels now real compiled SPIR-V 1.3)

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

All remaining scope items resolved 2026-06-12:

**VKSPIRV-001 — Real SPIR-V kernels (resolved 2026-06-12)**

All 8 raster kernels in `backend_vulkan_spirv_raster_blobs.spl` now contain
real compiled SPIR-V 1.3 modules (not stubs):
- `spirv_rect_outline` 2584B — draws border pixels, LocalSize 16×16
- `spirv_circle_filled` 2576B — `dx²+dy² <= r²` distance check, LocalSize 16×16
- `spirv_circle_outline` 2656B — ring check `(r-1)² <= dx²+dy² <= r²`, LocalSize 16×16
- `spirv_line` 2576B — parametric line, LocalSize 256×1
- `spirv_rounded_rect` 3680B — integer SDF corner check, LocalSize 16×16
- `spirv_triangle_filled` 3212B — barycentric edge function, LocalSize 16×16
- `spirv_gradient_rect` 3296B — per-channel RGBA lerp, LocalSize 16×16
- `spirv_blit` 1804B — src→fb copy (binding 0=fb, 1=src), LocalSize 16×16

All blobs assembled with `spirv-as --target-env vulkan1.1` (SPIRV-Tools v2025.1)
and validated with `spirv-val --target-env vulkan1.1`. Round-trip verification
confirmed. Comment block in `backend_vulkan_spirv.spl` updated to remove
"placeholder" language.

**rt_vulkan_init interpreter crash (confirmed non-reproducible 2026-06-12)**

`rt_vulkan_init()` does NOT crash in the interpreter. With lavapipe ICD at
`/usr/share/vulkan/icd.d/lvp_icd.json`, `rt_vulkan_init()` returns `true`
successfully. `VulkanBackend.init(4,4)` and `clear()` also succeed without error.
The original crash documented here was resolved in prior work. No code changes
needed for this item.

Both specs remain 22/22 green (interpreter mode).

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

