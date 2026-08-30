# macOS Vulkan ProcessingIR live readback parity

This is a prepared-host Darwin gate. It must not convert Linux evidence,
Draw IR-only evidence, CPU mirrors, or an unavailable host into a ProcessingIR
PASS.

## Shared Steps

1. `step("negotiate processing backend")`
2. `step("submit exact processing workload")`
3. `step("validate device receipt")`

## Prerequisites

- macOS with a working Vulkan loader/device and permission to launch and
  capture the native window.
- Current source checkout with the trusted self-hosted Vulkan build admitted by
  `scripts/check/build-macos-gpu-2d-live-native.shs`.
- Trusted provider artifacts: `build/sffi/libspl_winit.dylib`,
  `build/sffi/libsimple_runtime_wm.dylib`, and
  `build/sffi/libsimple_runtime_c_wm.dylib`.
- Trusted manifest:
  `build/macos_gpu_2d_live_native/vulkan/trusted-build.env`.
- macOS `screencapture`, `sips`, accessibility permission, and the canonical
  window/input tools used by the checker.

## Command

Run the system spec on the prepared host:

```sh
SIMPLE_LIB=src bin/simple test \
  test/03_system/check/macos_vulkan_processing_ir_live_readback_parity_spec.spl \
  --mode=interpreter
```

The spec invokes the canonical live producer directly:

```sh
sh scripts/check/check-macos-vulkan-2d-live-evidence.shs
```

## Required Receipt

The canonical receipt is:
`build/tmp/macos_vulkan_2d_live_evidence/runtime_receipt.env`.

A Darwin PASS additionally requires these ProcessingIR-specific keys in that
receipt, using the native producer field names under the macOS namespace:

```text
gpu_2d_live_processing_ir_status=pass
gpu_2d_live_processing_ir_reason=ok
gpu_2d_live_processing_ir_completed=true
gpu_2d_live_processing_ir_backend=vulkan
gpu_2d_live_processing_ir_count=64
gpu_2d_live_processing_ir_expected_checksum=1082179840
gpu_2d_live_processing_ir_actual_checksum=1082179840
gpu_2d_live_processing_ir_values_exact=true
gpu_2d_live_processing_ir_readback_source=device_readback
gpu_2d_live_processing_ir_handle=<positive integer>
gpu_2d_live_processing_ir_identity=<positive integer>
gpu_2d_live_processing_ir_mismatch_count=0
gpu_2d_live_processing_ir_cpu_fallback=false
```

The canonical harness emits this block from
`processing_ir_execute_vulkan(processing_ir_fill_u32(...))` before Engine2D
initialization. The canonical checker validates every admission field before
accepting the Vulkan receipt.

On a stage-4 failure, the harness retains result reason, completion, count,
checksums, exactness, mismatch count, backend handle, and device identity
together with the generic failure fields in one file write. A failure report
therefore cannot discard the backend cause or expose a partial receipt.

## Native SPIR-V ABI

The no-GC synchronous Vulkan I/O owner keeps the tagged Simple-array ABI only
for interpreter execution. Native execution passes the SPIR-V data pointer and
byte length to `rt_vulkan_compile_spirv_raw`, matching the established
Engine2D native boundary. This prevents AOT code from presenting a native
Simple array as the provider's raw byte input.

## Retained Evidence

- Receipt: `build/tmp/macos_vulkan_2d_live_evidence/runtime_receipt.env`
- Evidence: `build/tmp/macos_vulkan_2d_live_evidence/evidence.env`
- Capture: `build/tmp/macos_vulkan_2d_live_evidence/vulkan_3840x2160_300dpi.ppm`
  and `.png`
- Launch/window logs: `launch.out`, `launch.err`, and `window.env` in the same
  directory.
- Build report: `doc/09_report/macos_vulkan_2d_live_evidence_<UTC-date>.md`

## Ownership

- Owner: Ramanujan, macOS Vulkan evidence lane.
- Merge owner: Codex.
- Final reviewer: highest-capability model, read-only after integration.

## Pending Semantics

On non-macOS hosts the spec emits one pending result and returns. It does not
run the checker or inspect Linux receipts. On macOS, missing device, missing
ProcessingIR fields, checksum mismatch, nonpositive provenance, mismatch, or
fallback is a failure, never a pending success. Prepared-host execution is
still `PREPARED-HOST UNRUN` until the complete receipt block is emitted and
retained.
