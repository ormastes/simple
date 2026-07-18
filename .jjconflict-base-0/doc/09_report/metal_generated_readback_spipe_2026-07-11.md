# Metal Generated 2D Readback Evidence

Date: 2026-07-11

| Field | Value |
| --- | --- |
| metal_generated_2d_readback_status | pass |
| metal_generated_2d_readback_reason | gpu-readback-verified |
| metal_generated_2d_readback_backend_name | metal |
| metal_generated_2d_readback_metallib | build/portable-compute-metal-fixed/toolchains/simple_2d_optimization.metallib |
| metal_generated_2d_readback_metallib_bytes | 19658 |
| metal_generated_2d_readback_runtime_present | true |
| metal_generated_2d_readback_metal_tool_present | true |
| metal_generated_2d_readback_metallib_tool_present | true |
| metal_generated_2d_readback_module_verified | true |
| metal_generated_2d_readback_submit_attempted | true |
| metal_generated_2d_readback_readback_available | true |
| metal_generated_2d_readback_host_upload_available | true |
| metal_generated_2d_readback_expected_checksum | 23825409424378293188 |
| metal_generated_2d_readback_actual_checksum | 23825409424378293188 |
| metal_generated_2d_readback_mismatch_count | 0 |
| metal_generated_2d_readback_fill_checksum | 7254485133350916837 |
| metal_generated_2d_readback_fill_expected | 7254485133350916837 |
| metal_generated_2d_readback_copy_checksum | 6221106316586294309 |
| metal_generated_2d_readback_copy_expected | 6221106316586294309 |
| metal_generated_2d_readback_alpha_checksum | 6000179358840187557 |
| metal_generated_2d_readback_alpha_expected | 6000179358840187557 |
| metal_generated_2d_readback_scroll_checksum | 4349638615600894485 |
| metal_generated_2d_readback_scroll_expected | 4349638615600894485 |
| metal_generated_2d_readback_ops | fill,copy,alpha,scroll |
| metal_generated_2d_readback_required_path | 'Simple emitter -> runtime MSL compile -> MTLDevice -> host upload -> compute pipeline -> submit -> wait -> host download -> per-op hashes; separate generated source -> metallib validation' |

Generated Metal evidence has two explicit proofs: the native tools validate a metallib built from Simple-emitted MSL, while the runtime harness independently compiles the same current emitter output through Metal SFFI and executes it. The harness does not claim to load the metallib. Runtime proof is fail-closed until device/pipeline/encoder calls, a patterned host upload, submit, synchronization, host download, and position-sensitive per-op hashes all succeed.

## Host Validation Checklist (Darwin/macOS)
- Ensure Xcode command-line tools are installed and discoverable: xcode-select --install.
- Validate toolchain and runtime visibility: xcrun --find metal, xcrun --find metallib, system_profiler SPDisplaysDataType.
- Refresh and rebuild generated toolchains:
  SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-portable-compute-toolchains.shs
- Run proof lane directly:
  SIMPLE_BIN=bin/simple sh scripts/check/check-metal-generated-2d-readback.shs
- Promote through platform aggregate:
  SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
