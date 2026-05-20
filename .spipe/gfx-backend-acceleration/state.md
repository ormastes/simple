# SStack State: gfx-backend-acceleration

## Status: CLOSED — 2026-05-20

## User Request
> All 13 acceleration agents (A-M) from doc/03_plan/agent_tasks/graphics_backend_acceleration.md

## Task Type
feature

## Refined Goal
> Implement all graphics backend acceleration work: probe contract, Vulkan/CUDA/Metal/WebGPU proofs, CPU SIMD linkage, duplication reduction, system test matrix, C-vs-Simple perf, Tauri equiv perf, Chrome render perf, WM optimization, and rendering optimization providers.

## Acceptance Criteria
- [x] AC-1: BackendProbeResult with typed unavailable/fallback/success states
- [x] AC-2: Strict backend creation (no silent fallback) + existing fallback preserved
- [x] AC-3: Vulkan SPIR-V or feature-gated shader path (no unsupported GLSL runtime)
- [x] AC-4: Vulkan clear/rect/readback smoke with typed diagnostics
- [x] AC-5: CUDA device memory rendering/readback proof with diagnostics
- [x] AC-6: Metal command queue/pipeline/dispatch/completion/readback proof
- [x] AC-7: WebGPU explicit stub mode + adapter diagnostics
- [x] AC-8: CPU SIMD optimization provider metadata gated by target features
- [x] AC-9: Engine2D shared helpers extracted (clip/mask, pixel pack, text fallback, upload/download)
- [x] AC-10: System test matrix with unavailable/fallback/hardware statuses + perf fields
- [x] AC-11: C-vs-Simple 2D perf runner with frame timing, pixels/sec, RSS
- [x] AC-12: Tauri-equivalent perf runner with startup/window/resize/IPC metrics
- [x] AC-13: Chrome-vs-Simple web render perf with FPS/dropped/memory metrics
- [x] AC-14: WM dirty-rect tracking, present batching, timing counters
- [x] AC-15: Rendering optimization plugin providers with hit/change counters

## Phase Checklist
- [x] 1-dev — 2026-05-17
- [x] 2-research — 2026-05-17 (skipped: plan doc exists)
- [x] 3-arch — 2026-05-17 (skipped: plan doc exists)
- [x] 4-spec — 2026-05-17 (specs by implement agents)
- [x] 5-implement — 2026-05-19
- [x] 6-refactor — 2026-05-19
- [x] 7-verify — 2026-05-19
- [x] 8-ship — 2026-05-19

## Phase Outputs

### 1-dev
15 ACs covering all 13 agents (A-M). Agents F+M combined (shared compiler scope).

### 5-implement
<pending>
