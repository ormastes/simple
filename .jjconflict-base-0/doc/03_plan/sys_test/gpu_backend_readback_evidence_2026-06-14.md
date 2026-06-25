# GPU Backend Readback Evidence Plan - 2026-06-14

## Local Linux Evidence

- Vulkan: `scripts/check/check-vulkan-engine2d-readback.shs` passed with
  `vulkan_engine2d_readback_status=pass`, present/readback exercised, and zero
  mismatches. Report: `doc/09_report/vulkan_engine2d_readback_2026-06-14.md`.
- CUDA: `scripts/check/check-cuda-generated-2d-readback.shs` passed with
  `cuda_generated_2d_readback_status=pass`, fill/copy/alpha/scroll checksum
  matches, and zero mismatches. Report:
  `doc/09_report/cuda_generated_2d_readback_2026-06-14.md`.
- ROCm/HIP: `scripts/check/check-rocm-generated-2d-readback.shs` recorded
  `rocm_generated_2d_readback_status=unavailable` because `hipcc`/ROCm probe
  tooling is absent on this host. Report:
  `doc/09_report/rocm_generated_2d_readback_2026-06-14.md`.
- Metal: `scripts/check/check-metal-generated-2d-readback.shs` recorded
  `metal_generated_2d_readback_status=unavailable` because this is Linux and
  the Metal/Xcode toolchain is absent. Report:
  `doc/09_report/metal_generated_2d_readback_2026-06-14.md`.

## Platform Follow-Up

- macOS: run `scripts/check/check-metal-generated-2d-readback.shs`,
  `scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs`, and
  `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` on a Mac with
  Xcode command-line tools. Native Metal readback must report submit/readback
  available and zero mismatches.
- Windows: run DirectX native evidence after D3D11/D3D12 setup, then compare
  against Linux DXVK/vkd3d Vulkan shim evidence documented in
  `doc/07_guide/ui/directx_on_linux_setup.md`.
- ROCm/HIP: rerun the ROCm generated 2D readback script on a host with `hipcc`,
  `rocminfo`, and a supported AMD GPU. Unavailable status on this NVIDIA Linux
  host is not a pass for HIP production readiness.
