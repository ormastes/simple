<!-- codex-research -->
# Graphics Backend Acceleration Feature Options

Date: 2026-05-16

## Option A: Backend Proof Only

Description: add strict forced-backend smoke tests for CPU, CUDA, OpenCL,
Vulkan, Metal, and WebGPU.

Pros:
- Lowest risk.
- Quickly catches silent fallback.

Cons:
- Does not compare Simple against C, Chrome, or Tauri.
- Does not drive optimization work.

Effort: M, 8-14 files.

## Option B: Common Acceleration Interface

Description: preserve `RenderBackendCore` and `RenderBackendAdv`, add shared backend diagnostics and strict creation APIs, and test backend proof.

Pros:
- Aligns with existing architecture.
- Creates a common interface for 2D, web, WM, and future 3D paths.

Cons:
- Still not performance-first unless benchmarks are added.

Effort: L, 16-28 files.

## Option B2: Performance-First Backend Proof

Description: extend Option B with reference benchmarks:

- C vs Simple direct 2D;
- Rust+Tauri vs Simple GUI app;
- Chrome vs Simple web renderer;
- CPU scalar vs CPU SIMD;
- CUDA/OpenCL/Vulkan/Metal/WebGPU backend vs CPU reference.

Pros:
- Directly supports the updated goal.
- Prevents "backend exists" from being confused with "backend is fast".
- Gives concrete targets for Engine2D, web engine, window manager, backends, and optimization plugins.

Cons:
- Requires benchmark infrastructure before some implementation work.
- Tauri and Chrome comparison requires platform-dependent setup.
- OpenCL proof requires a host ICD or explicit unavailable evidence.

Effort: XL, 30-45 files.

## Option D: Full Backend Capsule Refactor

Description: introduce MDSOC-style capsules for `render.engine2d`, `surface.host`, `gpu.device`, and `compiler.optimization.simd`, then remove duplication across backend families.

Pros:
- Best long-term architecture.
- Strong duplication reduction.

Cons:
- Highest risk if done before measurements.

Effort: XL, 40+ files.

## Recommended Selection

Select Option B2 first. Use measured gaps to drive Option D cleanup.

## Candidate Requirements For B2

- REQ-GFX-PERF-001: matched C and Simple direct 2D benchmark apps.
- REQ-GFX-PERF-002: matched Rust+Tauri and Simple GUI workflow benchmarks.
- REQ-GFX-PERF-003: Chrome and Simple web-rendering timing plus pixel reports.
- REQ-GFX-PERF-004: strict backend selection fails on fallback.
- REQ-GFX-PERF-005: WM exposes frame pacing, event-loop, dirty-rect, and present timings.
- REQ-GFX-PERF-006: SIMD/vectorization providers are declared through Simple optimization plugin metadata.
- REQ-GFX-PERF-007: OpenCL generated-kernel evidence records ICD/platform,
  artifact format, program build status, kernel submit status, sync/readback
  status, and fallback reason separately from CUDA evidence.

## Session-Managed Backend Requirements

Covered by `test/03_system/app/graphics_backend/feature/graphics_3d_session_managed_backend_spec.spl`:

- REQ-GFX-001: the graphics backend capability model reports backend kind
  and target architecture, and rejects unknown backend kinds.
- REQ-GFX-002: legacy no-session constructors map to `LegacyNoSession` mode
  and never enable managed caches.
- REQ-GFX-003: managed and perf-isolated sessions reject mutable resource
  sharing across modes while still allowing immutable capability-table sharing.
- REQ-GFX-004: a single backend policy binds across 2D, 2D game, 3D, web
  renderer, GUI, and WM surfaces.
- REQ-GFX-005: optimization provider state is keyed by provider, backend,
  and policy hash, and stays isolated between managed and perf-exclusive state.
- REQ-GFX-006: the public API is a Pure Simple / C ABI native boundary that
  rejects a Rust runtime backend requirement.
- REQ-GFX-007: capability records cover ARM32, ARM64, RISC-V32, and RISC-V64
  targets.
