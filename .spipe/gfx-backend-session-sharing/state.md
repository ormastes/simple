# SStack State: gfx-backend-session-sharing

## User Request
> next task from the plan — graphics_backend_session_sharing (10 agents A-J)

## Task Type
feature

## Refined Goal
> Implement backend session sharing: session contract, per-backend integration (CUDA/Vulkan/Metal/WebGPU/CPU), Engine2D session-aware constructors, web/WM adoption, ARM/RISC-V validation, and mode-separation tests.

## Acceptance Criteria
- [x] AC-1: backend_session.spl with mode/kind/policy/handle/error + create/retain/release/probe APIs
- [x] AC-2: CUDA session retains primary context, caches PTX modules/kernels
- [x] AC-3: Vulkan session owns device/queue/allocator/pipeline/command pools
- [x] AC-4: Metal session owns MTLDevice/queue/pipeline states (macOS-only guard)
- [x] AC-5: WebGPU session owns adapter/device/queue with real/stub diagnostics
- [x] AC-6: CPU SIMD session with scalar/SIMD provider selection, target-gated
- [x] AC-7: Engine2D session-aware constructors + read-only perf counters
- [x] AC-8: Web engine RenderSurfaceSession + WM session adoption
- [x] AC-9: ARM/RISC-V 32/64 scalar session checks
- [x] AC-10: Mode separation tests (legacy compat, managed sharing, perf isolation)

## Phase Checklist
- [x] 1-dev — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [x] 5-implement — 2026-05-17
- [x] 6-refactor — 2026-05-17 (clean on first pass)
- [x] 7-verify — 2026-05-17
- [x] 8-ship — 2026-05-17

## Phase Outputs
### 1-dev
10 ACs, 10 agents (A-J). Plan at doc/03_plan/agent_tasks/graphics_backend_session_sharing.md.
### 5-implement
10 parallel Sonnet agents. 10 files created:
- src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl (255 lines) — session contract
- src/lib/nogc_sync_mut/gpu/engine2d/cuda_session.spl (183 lines) — CUDA PTX cache
- src/lib/nogc_sync_mut/gpu/engine2d/vulkan_session.spl (183 lines) — Vulkan SPIR-V + thread policy
- src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl (171 lines) — Metal macOS guard
- src/lib/nogc_sync_mut/gpu/engine2d/webgpu_session.spl (140 lines) — real/stub diagnostics
- src/lib/nogc_sync_mut/gpu/engine2d/cpu_simd_session.spl (175 lines) — target-gated kernels
- src/lib/gc_async_mut/gpu/engine2d/engine2d_session.spl (248 lines) — Engine2D API migration
- src/lib/gc_async_mut/gpu/engine2d/web_wm_session.spl (210 lines) — Web/WM adoption
- src/lib/nogc_sync_mut/gpu/engine2d/arm_riscv_session.spl (185 lines) — ARM/RISC-V validation
- test/unit/gpu/backend_session_sharing_spec.spl (228 lines) — 20 mode separation tests
### 7-verify
20/20 tests PASS (108ms). Commit d75c684d2d pushed to origin/main.
