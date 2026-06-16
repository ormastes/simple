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

Local status: host-unavailable; no AMD GPU is visible and `rocminfo` is absent.

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
3. Add native DirectX and real WebGPU device-readback runs; provenance-only
   `swapchain_present` and `surface_upload` rows are not production proof.
4. Keep local NVIDIA Vulkan/CUDA/OpenCL as current passing Linux evidence.
