<!-- codex-research -->
# Accelerated Shared UI Backend Architecture - NFR Options

Date: 2026-06-03

## NFR Option 1: Evidence-Only Baseline

Description:
- All unavailable backends report typed unavailable status.
- No accelerated claim is accepted without backend, artifact, device, fallback,
  and readback provenance.
- `doc/06_spec` contains no executable `.spl` specs.

Pros:
- CI-friendly and portable.

Cons:
- Does not enforce performance competitiveness.

Effort: S.

## NFR Option 2: Backend Comparison Targets

Description:
- Measure cold start, warm start, binary size, p50/p95 frame time, p95 input to
  paint latency, RSS, and readback time for pure Simple, Tauri, Electron,
  NodeJS/browser, CPU scalar, CPU SIMD, CUDA, OpenCL, Vulkan, Metal, and WebGPU
  where available.
- Simple direct 2D CPU SIMD must be at or below scalar p95 frame time and must
  report architecture facts for x86, Arm, or RISC-V.
- CUDA and OpenCL generated kernels must both report artifact build time,
  module load time, submit time, sync time, readback checksum, and fallback
  status.
- Shell adapters must not run full-tree scans, shell-outs, or retry sleeps in
  hot request paths.

Pros:
- Directly supports startup/bin-size/perf comparisons requested in the goal.

Cons:
- Requires benchmark harness work and platform normalization.

Effort: M.

## NFR Option 3: Release-Gate Targets

Description:
- Linux: CPU scalar/SIMD, OpenCL ICD where available, CUDA on NVIDIA, Vulkan.
- macOS: CPU scalar/SIMD, Metal, Tauri/Electron/pure Simple shell comparison.
- Windows: CPU scalar/SIMD, OpenCL ICD where available, CUDA on NVIDIA,
  Electron/Tauri shell comparison.
- Every release gate records hardware, OS, compiler mode, backend, artifact
  format, sample count, and max RSS.

Pros:
- Strongest production signal.

Cons:
- Requires multi-platform CI and hardware lanes.

Effort: L.

## Recommended Selection

Use NFR Option 2 for implementation planning. Keep NFR Option 1 as the first CI
gate until hardware-backed OpenCL/CUDA/Metal runners exist.
