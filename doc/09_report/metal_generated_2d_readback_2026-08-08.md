# Metal Generated 2D Readback Evidence

Date: 2026-08-08

| Field | Value |
| --- | --- |
| metal_generated_2d_readback_status | unavailable |
| metal_generated_2d_readback_reason | trusted-artifact-admission-failed |
| metal_generated_2d_readback_backend_name | metal |
| metal_generated_2d_readback_metallib | build/metal_generated_2d_readback/toolchains/simple_2d_optimization.metallib |
| metal_generated_2d_readback_metallib_bytes | 0 |
| metal_generated_2d_readback_provenance_status | unavailable |
| metal_generated_2d_readback_trusted_manifest | /home/ormastes/dev/pub/simple/build/macos_gpu_2d_live_native/metal/trusted-build.env |
| metal_generated_2d_readback_trusted_manifest_sha256 |  |
| metal_generated_2d_readback_toolchain_manifest | build/metal_generated_2d_readback/toolchains/evidence.env |
| metal_generated_2d_readback_toolchain_manifest_sha256 |  |
| metal_generated_2d_readback_simple_bin_path |  |
| metal_generated_2d_readback_simple_bin_sha256 |  |
| metal_generated_2d_readback_generated_source | build/metal_generated_2d_readback/toolchains/simple_2d_optimization.metal |
| metal_generated_2d_readback_generated_source_sha256 |  |
| metal_generated_2d_readback_metallib_sha256 |  |
| metal_generated_2d_readback_harness_exit_code | not-run |
| metal_generated_2d_readback_runtime_present | false |
| metal_generated_2d_readback_metal_tool_present | false |
| metal_generated_2d_readback_metallib_tool_present | false |
| metal_generated_2d_readback_module_verified | false |
| metal_generated_2d_readback_submit_attempted | false |
| metal_generated_2d_readback_readback_available | false |
| metal_generated_2d_readback_expected_checksum | 0 |
| metal_generated_2d_readback_actual_checksum | 0 |
| metal_generated_2d_readback_ops | fill,copy,alpha,scroll |
| metal_generated_2d_readback_required_path | 'Simple emitter -> runtime MSL compile -> MTLDevice -> host upload -> compute pipeline -> submit -> wait -> host download -> per-op hashes; separate generated source -> metallib validation' |

Generated Metal evidence has two explicit proofs: the native tools validate a metallib built from Simple-emitted MSL, while the runtime harness independently compiles the same current emitter output through Metal SFFI and executes it. The harness does not claim to load the metallib. Runtime proof is fail-closed until trusted manifest admission binds the canonical Simple binary and generated source/metallib hashes, the harness exits zero, and device/pipeline/encoder calls, a patterned host upload, submit, synchronization, host download, and position-sensitive per-op hashes all succeed.

## Host Validation Checklist (Darwin/macOS)
- Ensure Xcode command-line tools are installed and discoverable: xcode-select --install.
- Validate toolchain and runtime visibility: xcrun --find metal, xcrun --find metallib, system_profiler SPDisplaysDataType.
- Run proof lane directly after producing the canonical trusted-build manifest:
  SIMPLE_LIB=src sh scripts/check/check-metal-generated-2d-readback.shs
- Promote through platform aggregate:
  SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
