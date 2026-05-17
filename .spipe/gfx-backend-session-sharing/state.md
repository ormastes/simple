# SStack State: gfx-backend-session-sharing

## User Request
> next task from the plan — graphics_backend_session_sharing (10 agents A-J)

## Task Type
feature

## Refined Goal
> Implement backend session sharing: session contract, per-backend integration (CUDA/Vulkan/Metal/WebGPU/CPU), Engine2D session-aware constructors, web/WM adoption, ARM/RISC-V validation, and mode-separation tests.

## Acceptance Criteria
- [ ] AC-1: backend_session.spl with mode/kind/policy/handle/error + create/retain/release/probe APIs
- [ ] AC-2: CUDA session retains primary context, caches PTX modules/kernels
- [ ] AC-3: Vulkan session owns device/queue/allocator/pipeline/command pools
- [ ] AC-4: Metal session owns MTLDevice/queue/pipeline states (macOS-only guard)
- [ ] AC-5: WebGPU session owns adapter/device/queue with real/stub diagnostics
- [ ] AC-6: CPU SIMD session with scalar/SIMD provider selection, target-gated
- [ ] AC-7: Engine2D session-aware constructors + read-only perf counters
- [ ] AC-8: Web engine RenderSurfaceSession + WM session adoption
- [ ] AC-9: ARM/RISC-V 32/64 scalar session checks
- [ ] AC-10: Mode separation tests (legacy compat, managed sharing, perf isolation)

## Phase Checklist
- [x] 1-dev — 2026-05-17
- [x] 2-4 — skipped (plan doc comprehensive)
- [ ] 5-implement
- [ ] 6-refactor
- [ ] 7-verify
- [ ] 8-ship

## Phase Outputs
### 1-dev
10 ACs, 10 agents (A-J). Plan at doc/03_plan/agent_tasks/graphics_backend_session_sharing.md.
### 5-implement
<pending>
