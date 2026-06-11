# Engine2D Vulkan GLSL/SPIR-V Parity Closure

Status: likely-fixed (triaged 2026-06-11, evidence: resolved/fixed content in body)

Date: 2026-05-29

## Summary

The original Engine2D Vulkan blocker is closed for the focused Linux live
Vulkan gate. `VulkanBackend` now initializes with validated SPIR-V for clear and
filled-rect kernels, dispatches compute work, presents, and reads pixels back
through the strict smoke path.

Remaining scope is broader primitive parity beyond the strict clear and
filled-rect coverage, plus platform-specific Metal/iOS evidence tracked in the
GUI renderer restart plan.

## Fix Evidence

- Active Vulkan backend/session setup now uses `vulkan_sffi_compile_spirv(...)`
  for clear and filled-rect shaders instead of the unsupported GLSL compile
  path.
- Interpreter Vulkan SFFI now registers and implements
  `rt_vulkan_compile_spirv`, `rt_vulkan_copy_to_buffer`, and
  `rt_vulkan_read_buffer_bytes`.
- SPIR-V bytes are copied into aligned `u32` words before
  `vkCreateShaderModule`.
- Push constants now accept `u8` array values, and Simple push-constant packing
  helpers return updated arrays instead of relying on free-function argument
  mutation.
- Compute dispatch now records a `vkCmdPipelineBarrier` from shader writes to
  host reads before command-buffer completion.
- `BackendProbeResult.is_ok()` was added as a compatibility alias for strict
  probe checks.

## Verification

```bash
SIMPLE_LIB=/home/ormastes/dev/pub/simple/src \
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/nvidia_icd.json \
__EGL_VENDOR_LIBRARY_FILENAMES=/usr/share/glvnd/egl_vendor.d/10_nvidia.json \
timeout 180s src/compiler_rust/target/debug/simple test test/02_integration/rendering/vulkan_strict_spec.spl --mode=interpreter --clean --format json
```

Result: `success: true`, `total_passed: 18`, `total_failed: 0`,
`duration_ms: 9772`. The JSON file entry still included
`error: "Process exited with code -1"` despite the successful assertion result;
that is a runner shutdown/reporting quirk to track separately if it becomes
release-blocking.

Additional focused checks:

- `engine2d_cpu_vulkan_parity_spec`: `3/3`
- `vulkan_spirv_spec`: `12/12`
- `cargo check -p simple-compiler`: pass with two existing `last_value`
  warnings

