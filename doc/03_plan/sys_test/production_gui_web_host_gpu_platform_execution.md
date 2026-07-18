# Production GUI/Web Host-GPU Platform Execution Plan

This plan extends the Linux passing gate in
`scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
to the platform-specific backends that cannot be promoted from provenance on
the current Linux host.

## Current Baseline

- Linux aggregate command:
  `SIMPLE_BIN=src/compiler_rust/target/debug/simple sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`
- Current Linux proof:
  `production_gui_web_host_gpu_queue_readback_status=pass`,
  `production_runtime_queue_integration_status=pass`,
  `browser_frame_queue_status=pass`,
  `same_frame_gpu_backend_readback_status=pass`.
- Current partial matrix:
  Vulkan GUI/web same-frame `device_readback` passes; CUDA/OpenCL child
  readback wrappers pass; WebGPU real `device_readback` is unavailable on the
  latest local proof and WebGPU `surface_upload` remains provenance-only; Metal
  and ROCm/HIP are host-unavailable; DirectX remains native-pending.

## Promotion Rules

A backend may move from host-unavailable or provenance-only to production proof
only when its evidence contains all of:

- A backend child wrapper or BrowserBackend probe exit code of `0`.
- A positive backend handle from the concrete backend, not a synthetic queue
  handle.
- Same-frame readback source `device_readback`.
- Nonzero pixel count and checksum matching the backend fixture or
  BrowserBackend frame oracle.
- A report path under `build/production_gui_web_host_gpu_queue_readback/<backend>/`.
- A normal-LLM verification status of `pass` from the generated evidence env.

Presentation-only evidence such as `swapchain_present` and upload-only evidence
such as `surface_upload` must remain `provenance_only` and
`not_device_readback`.

## Platform Tasks

### Linux Vulkan/CUDA/OpenCL Queue Proof

Host requirements: Linux host with the repository-managed Vulkan/BrowserBackend
fixture and generated 2D CUDA/OpenCL child wrappers available. These are part of
the current Linux queue-integration gate rather than remaining matrix gaps.

Commands:

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-vulkan-engine2d-readback.shs

SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-cuda-generated-2d-readback.shs

SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-opencl-generated-2d-readback.shs

SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Promotion keys:
`readback_vulkan_verdict=pass`, `readback_cuda_verdict=pass`,
`readback_opencl_verdict=pass`,
`readback_cuda_submit_attempted=true`,
`readback_cuda_readback_available=true`,
`readback_opencl_submit_attempted=true`,
`readback_opencl_readback_available=true`,
`same_frame_gpu_backend_readback_status=pass`,
`browser_first_gpu_readback_source=device_readback`, and
`production_runtime_queue_integration_status=pass`. The aggregate must not
report Linux queue integration as pass if any of the Vulkan, CUDA, or OpenCL
child readback verdicts are missing, not `pass`, or if CUDA/OpenCL submit and
readback booleans are not `true`.

### macOS Metal

Host requirements: Darwin/macOS with Xcode command-line tools and Metal runtime.

Commands:

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-metal-generated-2d-readback.shs

SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Promotion keys:
`metal_generated_2d_readback_status=pass`,
`metal_generated_2d_readback_module_verified=true`,
`metal_generated_2d_readback_submit_attempted=true`,
`metal_generated_2d_readback_readback_available=true`, nonzero matching
expected/actual checksums, aggregate `readback_metal_verdict=pass`,
`metal_spark_task_status=pass`, `metal_normal_llm_verification_status=pass`,
and `metal_host_availability=host-available`.
The Metal wrapper self-test rejects missing submit/readback, zero per-op
checksums, and checksum mismatches.

### Windows DirectX

Host requirements: Windows with native D3D readback support, or an explicitly
documented DXVK host where the DirectX backend reports a real readback handle.

Commands:

```powershell
$env:SIMPLE_BIN="src/compiler_rust/target/debug/simple"
$env:SIMPLE_LIB="src"
& $env:SIMPLE_BIN test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_directx_spec.spl --mode=interpreter
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Promotion keys must replace provenance-only fields with a same-frame
`device_readback` proof: `directx_native_readback_status=pass`,
`directx_native_readback_source=device_readback`,
`directx_native_readback_backend_handle` positive, positive matching
expected/actual checksums, and
`directx_native_readback_wrapper_gate_status=pass`. The wrapper self-test
rejects zero or malformed handles, zero checksums, checksum mismatches, and
structured-contract-only provenance. Until then keep `directx_spark_task_status`
native-pending and
`directx_normal_llm_verification_status` native-pending rather than pass.

### ROCm/HIP

Host requirements: Linux with AMD GPU, ROCm/HIP runtime, compile tool, and
working HSACO/kernel launch path.

Commands:

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-rocm-generated-2d-readback.shs

SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Promotion keys:
`rocm_generated_2d_readback_status=pass`,
`rocm_generated_2d_readback_hsaco_bytes` positive,
`rocm_generated_2d_readback_module_verified=true`,
`rocm_generated_2d_readback_submit_attempted=true`,
`rocm_generated_2d_readback_readback_available=true`, nonzero matching
expected/actual checksums, aggregate `readback_rocm_verdict=pass`,
`rocm_spark_task_status=pass`, `rocm_normal_llm_verification_status=pass`,
and `rocm_host_availability=host-available`.
The ROCm wrapper self-test rejects missing submit/readback, zero per-op
checksums, and checksum mismatches.

### WebGPU

Host requirements: a browser/host runtime where `rt_webgpu_*` is backed by a
real WebGPU device and staging readback, not the default runtime stubs.

Commands:

```sh
SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
src/compiler_rust/target/debug/simple test test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_webgpu_spec.spl --mode=interpreter

sh scripts/check/check-webgpu-real-readback.shs

SIMPLE_BIN=src/compiler_rust/target/debug/simple SIMPLE_LIB=src \
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Promotion keys must prove `webgpu_upload_evidence_kind=device_readback` or an
equivalent backend-specific field, with nonnegative
`rt_webgpu_readback_checksum` and a positive surface/backend handle. The
standalone wrapper publishes `webgpu_real_readback_status=pass`,
`webgpu_real_readback_source=device_readback`, a positive
`webgpu_real_readback_backend_handle`, and positive matching expected/actual
checksums when a real `webgpu-real` host is available. The wrapper self-test
rejects zero or malformed handles, zero checksums, checksum mismatches, and
upload-only provenance so communication or surface-upload evidence cannot
masquerade as same-frame proof. The aggregate now consumes that same-frame
proof and reports `webgpu_spark_task_status=pass` and
`webgpu_normal_llm_verification_status=pass`; keep `surface_upload`
provenance-only.

## Normal-LLM Review Checklist

- Reject any backend promotion that does not include `device_readback`.
- Reject synthetic handles as backend integration proof.
- Confirm `doc/06_spec` contains no executable `.spl` files.
- Confirm the aggregate report still lists the platform matrix status and
  missing platforms accurately.
- Confirm platform work did not relax the Linux Vulkan/BrowserBackend, CUDA,
  or OpenCL child readback gates.
