# Simple Web Browser GPU Environment Matrix

## Local Host Snapshot

- Host: Ubuntu 24.04.4, Linux 6.8, x86_64.
- CPU/platform: AMD Family 17h / X399 class host.
- Visible GPUs: NVIDIA RTX A6000 and NVIDIA TITAN RTX.
- Vulkan: available through NVIDIA proprietary driver and Mesa llvmpipe.
- OpenCL: available through NVIDIA CUDA OpenCL.
- CUDA: available through NVIDIA driver.
- Metal: unavailable locally; requires Apple platform runtime and tools.
- AMD ROCm: unavailable locally; no `rocminfo`/ROCm probe tool and no visible AMD GPU.
- Emulation: QEMU x86_64 and aarch64 are installed; llvmpipe Vulkan CPU device is available.

## Local Evidence From 2026-06-16

- `sh scripts/check/check-vulkan-engine2d-readback.shs`: `overall=pass`,
  `backend_name=vulkan`, readback exercised, clear/rect mismatches `0`.
- `sh scripts/check/check-metal-generated-2d-readback.shs`:
  `status=unavailable`, `reason=missing-primary-tool`.
- `sh scripts/check/check-rocm-generated-2d-readback.shs`:
  `status=unavailable`, `reason=missing-primary-tool`.
- `sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs`:
  Linux GUI/web queue integration `pass`; Vulkan/CUDA/OpenCL readback `pass`;
  Metal/ROCm/DirectX/WebGPU remain missing native `device_readback` platforms.
- `sh scripts/check/check-webgpu-real-readback.shs`:
  `status=unavailable`, `reason=webgpu-real-probe-run-failed`,
  `source=not_device_readback`, `backend_handle=0`.

Fresh local evidence from 2026-06-16 follow-up:

- `build/vulkan-engine2d-readback/evidence.env` reports
  `vulkan_engine2d_readback_status=pass`, `backend_name=vulkan`,
  clear/rect mismatches `0`, and `blur_or_tolerance_used=false`.
- `doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md`
  reports `production_gui_web_host_gpu_queue_readback_status=pass`,
  Linux GUI/web queue integration `pass`, same-frame Vulkan/BrowserBackend
  `device_readback`, and platform matrix `partial` because Metal, ROCm,
  DirectX, and WebGPU still require native external host proof.
- `build/metal_generated_2d_readback/evidence.env` reports
  `metal_generated_2d_readback_status=unavailable`,
  `reason=missing-primary-tool`, no Metal runtime/tools, no submit, and no
  readback.
- `build/rocm_generated_2d_readback/evidence.env` reports
  `rocm_generated_2d_readback_status=unavailable`,
  `reason=missing-primary-tool`, ROCm probe tool absent, no submit, and no
  readback.
- `build/webgpu-real-readback/evidence.env` reports
  `webgpu_real_readback_status=unavailable`,
  `reason=webgpu-real-probe-run-failed`, `source=not_device_readback`,
  `backend_handle=0`, and checksum mismatch by absence (`0` vs `-1`).

## Environment Plans

### Linux NVIDIA Vulkan

Goal: keep Simple Web renderer/device readback proving a real Vulkan backend on
the local host.

Commands:

```sh
vulkaninfo --summary
sh scripts/check/check-vulkan-engine2d-readback.shs
```

Pass condition: Vulkan strict status and Engine2D CPU/Vulkan parity pass with
readback exercised and mismatches `0`.

Next local work: keep Vulkan readback requirements strict while treating the
full host-GPU matrix as partial until Metal, ROCm, DirectX, and WebGPU native
device-readback evidence exists.

### Linux NVIDIA CUDA/OpenCL

Goal: retain native NVIDIA fallback lanes for host GPU queue readback when Vulkan
is not the selected browser backend.

Commands:

```sh
clinfo
nvidia-smi --query-gpu=name,driver_version,memory.total --format=csv
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Pass condition: `readback_cuda_verdict=pass` and
`readback_opencl_verdict=pass` with submit and readback available.

### Linux Vulkan CPU Emulation

Goal: keep a software Vulkan fallback plan for CI or machines without usable
discrete GPU access.

Commands:

```sh
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.x86_64.json vulkaninfo --summary
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.x86_64.json sh scripts/check/check-vulkan-engine2d-readback.shs
```

Pass condition: backend reports Vulkan initialized through llvmpipe/lavapipe
and readback mismatches remain `0`. This is emulation evidence, not native GPU
performance evidence.

### macOS Metal

Goal: prove native Metal readback for Simple Web/Engine2D on Apple hardware.

Required host: macOS with Xcode command line tools, `xcrun`, `metal`,
`metallib`, and an available `MTLDevice`.

Commands:

```sh
sh scripts/check/check-metal-generated-2d-readback.shs
sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs
ELECTRON_BITMAP_TIMEOUT_SECS=60 sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
```

Pass condition: generated Metal readback and raw Metal framebuffer readback
report `pass`; production renderer parity wrapper must not use blur/tolerance.
The generated Metal wrapper self-test rejects missing submit/readback, zero
per-op checksums, and checksum mismatches.

Local status: host-unavailable on Linux; current acceptable reason is
`metal-requires-macos` for the production renderer wrapper and
`missing-primary-tool` for generated Metal readback.

### Linux AMD ROCm/HIP

Goal: prove AMD GPU generated 2D/readback through HIP/ROCm.

Required host: AMD GPU supported by ROCm, `rocminfo`, `hipcc`,
`libamdhip64`, `libhsa-runtime64`, and a valid `HIP_ARCH`.

Commands:

```sh
rocminfo
HIP_ARCH=gfx1100 sh scripts/check/check-portable-compute-toolchains.shs
HIP_ARCH=gfx1100 sh scripts/check/check-rocm-generated-2d-readback.shs
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Pass condition: ROCm module verified, submit attempted, readback available, and
per-op checksums match for fill/copy/alpha/scroll.
The ROCm wrapper self-test rejects missing submit/readback, zero per-op
checksums, and checksum mismatches.

Local status: host-unavailable; no AMD GPU is visible and `rocminfo` is absent.

### Windows DirectX Native

Goal: replace structured DirectX provenance with native DirectX device readback
for Simple Web/Engine2D on a Windows host.

Required host: Windows with a DirectX-capable GPU, working native Simple
runtime, and Direct3D staging/readback support. Linux DXVK/vkd3d setup can
validate local-prefix dependency wiring, but it is not native Windows
device-readback proof.

Commands:

```sh
sh scripts/check/check-directx-native-readback.shs
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Pass condition: `directx_native_readback_status=pass`, native wrapper gate
`pass`, positive backend/device handle, readback source `device_readback`, and
positive matching expected/actual checksum. The wrapper self-test rejects zero
or malformed handles, zero checksums, checksum mismatches, and
structured-contract-only provenance. The aggregate wrapper must no longer
report DirectX as only `structured_readback_contract` or `not_device_readback`.

Local status: not proven on this Linux host. Existing structured DirectX specs
are useful contract coverage only; production proof remains native-pending.

### Browser WebGPU Real Device

Goal: prove browser/WebGPU real device readback rather than surface-upload or
provenance-only evidence.

Required host: browser/runtime stack with real WebGPU enabled, cargo build of
`src/runtime/hosted` with `webgpu-real`, GPU adapter access, and a readback path
that emits `device_readback`.

Commands:

```sh
SIMPLE_WEBGPU_REAL_TIMEOUT_SECS=180 sh scripts/check/check-webgpu-real-readback.shs
sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

Pass condition: `webgpu_real_readback_status=pass`,
`webgpu_real_readback_source=device_readback`, positive
`webgpu_real_readback_backend_handle`, and positive matching expected/actual
checksum. The wrapper self-test rejects zero or malformed handles, zero
checksums, checksum mismatches, and upload-only provenance. `surface_upload`
remains provenance-only and does not satisfy production device-readback proof.

Local status: unavailable on the current host;
`webgpu-real-probe-run-failed`, `source=not_device_readback`,
`backend_handle=0`.

### QEMU / Other Emulation

Goal: use emulation only for platform boot/build coverage and software fallback
checks, not as proof of native Metal or AMD GPU execution.

Commands:

```sh
qemu-system-x86_64 --version
qemu-system-aarch64 --version
VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.x86_64.json sh scripts/check/check-vulkan-engine2d-readback.shs
```

Pass condition: QEMU availability is recorded separately from GPU proof;
llvmpipe/lavapipe Vulkan readback may satisfy software-emulated Vulkan fallback
only.

## Follow-Up Queue

1. Add a macOS Metal run to replace host-unavailable evidence with native Metal
   proof.
2. Add an AMD ROCm host run to replace host-unavailable evidence with HIP/ROCm
   submit/readback proof.
3. Add native DirectX and real WebGPU device-readback runs; structured DirectX
   contracts and WebGPU `surface_upload` rows are not production proof.
4. Keep local NVIDIA Vulkan/CUDA/OpenCL as current passing Linux evidence.
