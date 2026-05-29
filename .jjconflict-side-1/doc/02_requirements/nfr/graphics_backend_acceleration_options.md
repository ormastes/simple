<!-- codex-research -->
# Graphics Backend Acceleration NFR Options

Date: 2026-05-16

## NFR Option 1: Conservative CI Proof

Description:
- CPU-only default path passes.
- Strict GPU backend tests fail with typed unavailable diagnostics when unsupported.
- No hot-path subprocesses or full-tree scans during rendering.

Effort: S.

## NFR Option 2: Backend Production Targets

Description:
- Warm backend init under 250 ms for CPU/WebGPU and under 500 ms for CUDA/Vulkan/Metal after driver load.
- 1920x1080 clear+rect+blit smoke under 16.7 ms average on hardware backends after warmup.
- Readback measured separately from command time.
- Diagnostics report selected backend, device, feature gate, shader format, and fallback reason.

Effort: M.

## NFR Option 2B: Comparative Performance Targets

Description:
- Simple direct 2D CPU scalar within 1.25x of C for p50 frame time.
- Simple direct 2D CPU SIMD/native equal or better than C for fill, blit, and clipped-scroll before parity is claimed.
- Simple GUI app equal or better than Rust+Tauri on cold start or idle memory, and within 1.25x on p95 new-window, scroll, resize, and IPC.
- Simple web app-shell fixtures under 16.7 ms p95 frame time for 60 Hz scroll targets after warmup.
- Chrome comparison reports include both pixel compatibility and timing status.
- Every claim records hardware, OS, backend, compiler mode, feature flags, sample count, and active optimization providers.

Effort: M.

## NFR Option 3: Cross-Platform Release Gate

Description:
- Linux: CPU, CUDA on NVIDIA, Vulkan where available.
- macOS: CPU, Metal, WebGPU/wgpu.
- Windows: CPU, CUDA on NVIDIA, WebGPU/wgpu/D3D-class path where enabled.

Effort: L.

## Recommended Selection

Use NFR Option 2B for this feature. Keep NFR Option 1 as default CI and add NFR Option 3 once platform CI exists.

