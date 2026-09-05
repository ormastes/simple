# Metal Generated 2D Readback Evidence

Date: 2026-06-26

| Field | Value |
| --- | --- |
| metal_generated_2d_readback_status | pass |
| metal_generated_2d_readback_reason | gpu-readback-verified |
| metal_generated_2d_readback_metallib | build/metal_generated_2d_readback/toolchains/simple_2d_optimization.metallib |
| metal_generated_2d_readback_metallib_bytes | 15427 |
| metal_generated_2d_readback_runtime_present | true |
| metal_generated_2d_readback_metal_tool_present | true |
| metal_generated_2d_readback_metallib_tool_present | true |
| metal_generated_2d_readback_module_verified | true |
| metal_generated_2d_readback_submit_attempted | true |
| metal_generated_2d_readback_readback_available | true |
| metal_generated_2d_readback_fill_checksum | 2935174976 |
| metal_generated_2d_readback_fill_expected | 2935174976 |
| metal_generated_2d_readback_copy_checksum | 2935174976 |
| metal_generated_2d_readback_copy_expected | 2935174976 |
| metal_generated_2d_readback_alpha_checksum | 3753910144 |
| metal_generated_2d_readback_alpha_expected | 3753910144 |
| metal_generated_2d_readback_scroll_checksum | 53897584 |
| metal_generated_2d_readback_scroll_expected | 53897584 |
| metal_generated_2d_readback_ops | fill,copy,alpha,scroll |
| metal_generated_2d_readback_required_path | 'Metal source -> metallib -> MTLDevice -> compute pipeline -> command buffer/encoder -> submit -> wait -> buffer readback -> per-op checksums' |

Generated Metal evidence is intentionally fail-closed until a verified metallib module, Metal runtime device/pipeline/encoder handles, submit, synchronization, and readback checksum are all present.

## Host Validation Checklist (Darwin/macOS)
- Ensure Xcode command-line tools are installed and discoverable: xcode-select --install.
- Validate toolchain and runtime visibility: xcrun --find metal, xcrun --find metallib, system_profiler SPDisplaysDataType.
- Refresh and rebuild generated toolchains:
  SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-portable-compute-toolchains.shs
- Run proof lane directly:
  SIMPLE_BIN=bin/simple sh scripts/check/check-metal-generated-2d-readback.shs
- Promote through platform aggregate:
  SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
