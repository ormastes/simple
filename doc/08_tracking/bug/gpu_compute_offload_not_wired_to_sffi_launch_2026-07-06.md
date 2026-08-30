# GPU compute offload is not wired to real SFFI kernel launch (CUDA/HIP/Vulkan)

**Date:** 2026-07-06
**Area:** lib/nogc_async_mut/compute, lib/nogc_sync_mut/text_layout, lib/gpu/engine2d
**Status:** Open (honest gap — device execution unproven off Metal)

## Summary

The `std.compute` offload surface (`src/lib/nogc_async_mut/compute/backend_dispatch.spl`)
is a **payload-gated provenance simulation**: it always computes the CPU reference
and only *reports* GPU provenance when `SIMPLE_COMPUTE_GPU_PAYLOAD == backend_name`.
It never calls a real kernel launch (`rt_cuda_launch_kernel`, `vulkan_sffi_dispatch`,
`rocm_launch_kernel`, …). The font-offload gate
(`src/lib/nogc_sync_mut/text_layout/font_rasterizer.spl`) is likewise a
checksum-verified **env-var payload transport**, honest by construction
(no-payload→CPU, matching→GPU-reported, corrupt→reject) but not a device path.

The only backend with a proven real compile→launch→readback on real hardware is
**Metal**, via `src/lib/nogc_sync_mut/io/metal_sffi.spl` +
`test/05_perf/graphics_2d/metal_readback_proof_spec.spl` (macOS-gated,
`rt_metal_is_available` sentinel). CUDA, HIP/ROCm, and Vulkan have **no**
equivalent real-device readback proof.

## Vulkan compute — contained-wiring assessment (per parity task)

A real ash compute runtime exists (`vulkan_graphics_runtime_compute.rs`, 6
bit-exact kernels) and this host has a Vulkan device. Wiring
`dispatch_reduce_i64` to that runtime is **NOT a contained pure-Simple change**:
`backend_dispatch.spl` has no SFFI seam to `vulkan_sffi_dispatch` /
`compile_spirv` / `copy_from_buffer`; adding one is a new cross-layer bridge
(runtime/seed territory) plus a buffer-transport contract, not an in-place
session extension. Not attempted here — recorded rather than faked.

## Structural note (opposite of the common assumption)

In `src/lib/gc_async_mut/gpu/engine2d/`, the **CUDA / ROCm / OpenCL** sessions
already carry a rich `*SessionEvidence` class with checksum-validated readback
(matched / mismatch / readback-unavailable branches). The **Metal** and
**Vulkan** sessions are minimal (Metal: honest unavailable reasons + lifecycle
only; Vulkan: create/lifecycle only) — they lack that evidence/checksum-readback
structure. Session-evidence parity for Metal/Vulkan is a separate follow-up.

## Done in this change (structure/coverage parity only — NOT device execution)

- Extended the font-offload gate with a **Vulkan** branch (bitmap + vector
  paths in `font_rasterizer.spl`), mirroring the existing CUDA/ROCm/HIP/OpenCL
  env-transport checksum gate. Honest: no-payload→CPU, matching→GPU-reported,
  corrupt-checksum→reject. No device execution claimed.
- Extended `test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl` so
  every offload backend (CUDA, OpenCL, ROCm, HIP, Metal, Vulkan) asserts all
  three payload branches + the honest-unavailable
  (`production-gpu-dispatch-not-wired`) reason. 26 examples, 0 failures.

## Remaining work

1. Real CUDA readback proof mirroring the Metal perf spec (`rt_cuda_*` guard).
2. Real Vulkan SPIR-V dispatch+readback via a new `backend_dispatch`→SFFI seam.
3. Real ROCm/HIP hsaco launch+readback (`rt_rocm_*` guard).
4. `*SessionEvidence` + checksum-readback parity for the Metal and Vulkan
   engine2d sessions.
