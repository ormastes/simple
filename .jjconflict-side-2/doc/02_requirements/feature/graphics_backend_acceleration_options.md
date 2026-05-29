<!-- codex-research -->
# Graphics Backend Acceleration Feature Options

Date: 2026-05-16

## Option A: Backend Proof Only

Description: add strict forced-backend smoke tests for CPU, CUDA, Vulkan, Metal, and WebGPU.

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
- GPU backend vs CPU reference.

Pros:
- Directly supports the updated goal.
- Prevents "backend exists" from being confused with "backend is fast".
- Gives concrete targets for Engine2D, web engine, window manager, backends, and optimization plugins.

Cons:
- Requires benchmark infrastructure before some implementation work.
- Tauri and Chrome comparison requires platform-dependent setup.

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

