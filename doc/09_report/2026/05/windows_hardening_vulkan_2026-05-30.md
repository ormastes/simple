# Windows Hardening: Vulkan Engine2D

Date: 2026-05-30
Host: Windows, PowerShell, `src/compiler_rust/target/debug/simple.exe`

## Changes

- Replaced the stale `test/unit/app/ui/vulkan_renderer_spec.spl` import of
  retired `std.ui.gui.vulkan_ffi` with current `VulkanBackend` smoke coverage.
- Added Windows-safe Vulkan renderer checks:
  - backend construction without resolving old GUI FFI modules
  - explicit diagnostic when Vulkan initialization fails
  - clear/present/readback when Vulkan initializes
  - `draw_rect_filled` readback when Vulkan initializes
- Updated `test/perf/graphics_2d/bench_2d_vulkan.spl` to compile the same
  prevalidated SPIR-V blobs used by `VulkanBackend` instead of runtime GLSL.
  This avoids the Windows shaderc/glslang dependency that produced
  `FAIL: compile clear shader`.

## Verification

- `simple check` passed for:
  - `test/integration/rendering/engine2d_cpu_vulkan_parity_spec.spl`
  - `test/integration/rendering/vulkan_strict_spec.spl`
  - `test/unit/app/ui/vulkan_renderer_spec.spl`
  - `test/unit/app/ui/vulkan_window_spec.spl`
  - `test/perf/graphics_2d/bench_2d_vulkan.spl`
- `simple run test/unit/app/ui/vulkan_renderer_spec.spl`
  - 4 examples, 0 failures
- `simple run test/integration/rendering/vulkan_strict_spec.spl`
  - 18 examples, 0 failures
- `simple run test/perf/graphics_2d/bench_2d_vulkan.spl`
  - Vulkan device count: 2
  - selected device: Intel(R) UHD Graphics 770
  - shaders compiled OK
  - pipelines created OK
  - descriptor sets bound OK
  - `BENCH_RESULT scene=fill_1080p backend=vulkan_compute frames=100`

## Notes

- `simple test --clean` currently records file-level failures with no assertion
  detail for rendering specs on this Windows host, while direct `simple run`
  executes the same specs successfully. This is tracked as a later test-runner
  hardening issue for the full bootstrap/test step.
- The benchmark still reports interpreter fallback after completion because JIT
  type inference does not infer some `u8` literals in the imported SPIR-V blob.
  The interpreter path completes successfully and exercises Vulkan.
