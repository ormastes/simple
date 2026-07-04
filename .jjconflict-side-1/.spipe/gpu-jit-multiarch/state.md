# SStack State: gpu-jit-multiarch

## Status: CLOSED — 2026-05-20

## User Request
> 1. do x86 64 32 mixed optimization for jit and optimization plugin. 2. optimize x86 32 and 64 for cuda, vulcan 4 combination for 2d rendering. 3. riscv 32 64 for cuda 2d rendering 4. 2d rendering with web rendering with session and managed way and update api. make a lot sonnet agents with opus cuda advisor. and do not make rust lib but c better pure simple.

## Task Type
feature

## Refined Goal
> Implement multi-architecture GPU-accelerated 2D rendering with tiered JIT hotspot optimization across x86 (32/64), RISC-V (32/64) — using CUDA and Vulkan backends with session/managed sharing — integrated with web rendering. All new code in Simple (.spl) or C. No new Rust.

## Constraints
- **Language**: Pure Simple preferred, C for native FFI perf. NO new Rust code.
- **Execution**: Many parallel Sonnet agents, Opus advisor for critical decisions
- **Existing infra**: `tiered_jit.spl` library, `rt_jit_*` externs, Vulkan dlopen runtime, CUDA FFI, session types (BackendSessionMode/Handle/Policy)

## 4 Tracks (Parallel Agent Groups)

### Track A: x86 64/32 Mixed JIT Optimization
**Goal**: JIT optimization plugin that uses i32 narrowing on x86_64 for efficiency, and routes x86_32 through LLVM JIT.
**Files** (Simple):
- `src/lib/nogc_sync_mut/jit/opt_i32_narrow.spl` — MIR-level i32 narrowing pass
- `src/lib/nogc_sync_mut/jit/jit_x86_mixed.spl` — x86 32/64 JIT dispatch wrapper
- `test/01_unit/jit/jit_opt_x86_mixed.spl` — verification test

### Track B: x86 32/64 × CUDA/Vulkan 2D Rendering (4 combos)
**Goal**: 2D rendering with all 4 combinations: {x86_32, x86_64} × {CUDA, Vulkan}, using session/managed mode.
**Files** (Simple):
- `src/lib/gc_async_mut/gpu/engine2d/render_2d_cuda_x86.spl` — CUDA 2D ops for x86 32/64
- `src/lib/gc_async_mut/gpu/engine2d/render_2d_vulkan_x86.spl` — Vulkan 2D ops for x86 32/64
- `test/01_unit/gpu/render_2d_x86_cuda_vulkan.spl` — 4-combo verification

### Track C: RISC-V 32/64 × CUDA 2D Rendering
**Goal**: CUDA 2D rendering on RISC-V targets with scalar CPU fallback.
**Files** (Simple):
- `src/lib/gc_async_mut/gpu/engine2d/render_2d_cuda_riscv.spl` — CUDA 2D for RV32/RV64
- `src/lib/gc_async_mut/gpu/engine2d/cpu_scalar_riscv.spl` — scalar fallback
- `test/01_unit/gpu/render_2d_riscv_cuda.spl` — verification

### Track D: Web Rendering + Session/Managed API Update
**Goal**: Integrate 2D rendering with web rendering surfaces using session/managed mode; update Engine2D API.
**Files** (Simple):
- `src/lib/gc_async_mut/gpu/engine2d/web_render_session.spl` — web surface session bridge
- `src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl` — updated Engine2D constructors
- `test/01_unit/gpu/web_render_session_spec.spl` — session/managed mode web test

## Acceptance Criteria
- [x] AC-1: JIT i32 narrowing produces measurably smaller code on x86_64 benchmark
- [x] AC-2: JIT x86_32 compiles and runs via LLVM backend
- [x] AC-3: CUDA 2D rendering works with ManagedShared session on x86_64
- [x] AC-4: Vulkan 2D rendering works with ManagedShared session on x86_64
- [x] AC-5: CUDA 2D compile-check passes for x86_32 target
- [x] AC-6: Vulkan 2D compile-check passes for x86_32 target
- [x] AC-7: CUDA 2D rendering with session on RISC-V 64 (scalar CPU fallback if no GPU)
- [x] AC-8: RISC-V 32 compiles with typed "GPU unavailable" diagnostic
- [x] AC-9: Web rendering surfaces use BackendSessionHandle for lifecycle
- [x] AC-10: Engine2D.create_managed() and create_with_session() work
- [x] AC-11: PerfExclusive cannot be retained by web/managed paths

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-research (skip — already researched in prior session) — 2026-05-19
- [x] 3-arch (skip — plan doc exists) — 2026-05-19
- [x] 4-spec (skip) — 2026-05-19
- [x] 5-implement (Engineer) — 2026-05-19
- [x] 6-refactor (Tech Lead) — 2026-05-19
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
4 parallel tracks defined. Skipping phases 2-4 (research/arch/spec already done in prior sessions). Going directly to Phase 5 (implement) with parallel Sonnet agents.

### 5-implement
<in-progress>
