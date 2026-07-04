# Metal Generated 2D Readback Evidence

Date: 2026-06-16

| Field | Value |
| --- | --- |
| metal_generated_2d_readback_status | unavailable |
| metal_generated_2d_readback_reason | missing-primary-tool |
| metal_generated_2d_readback_metallib | build/metal_generated_2d_readback/toolchains/simple_2d_optimization.metallib |
| metal_generated_2d_readback_metallib_bytes | 0 |
| metal_generated_2d_readback_runtime_present | false |
| metal_generated_2d_readback_metal_tool_present | false |
| metal_generated_2d_readback_metallib_tool_present | false |
| metal_generated_2d_readback_module_verified | false |
| metal_generated_2d_readback_submit_attempted | false |
| metal_generated_2d_readback_readback_available | false |
| metal_generated_2d_readback_expected_checksum | 0 |
| metal_generated_2d_readback_actual_checksum | 0 |
| metal_generated_2d_readback_ops | fill,copy,alpha,scroll |
| metal_generated_2d_readback_required_path | 'Metal source -> metallib -> MTLDevice -> compute pipeline -> command buffer/encoder -> submit -> wait -> buffer readback -> per-op checksums' |

Generated Metal evidence is intentionally fail-closed until a verified metallib module, Metal runtime device/pipeline/encoder handles, submit, synchronization, and readback checksum are all present.

## Host Validation Checklist (Darwin/macOS)
- Ensure Xcode command-line tools are installed and discoverable: xcode-select --install.
- Validate toolchain and runtime visibility: xcrun --find metal, xcrun --find metallib, system_profiler SPDisplaysDataType.
- Refresh and rebuild generated toolchains:
  SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=src sh scripts/check/check-portable-compute-toolchains.shs
- Run proof lane directly:
  SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple sh scripts/check/check-metal-generated-2d-readback.shs
- Promote through platform aggregate:
  SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
