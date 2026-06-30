# SStack State: gpu-session-backends

## Status: CLOSED — 2026-05-20

## User Request
> impl cuda vulcan, x86/riscv 64 32 about doc/03_plan/agent_tasks/graphics_backend_session_sharing.md complete plan

## Task Type
feature

## Refined Goal
> Implement CUDA and Vulkan backend sessions plus CPU scalar/SIMD sessions for x86-64, RISC-V 64, and RISC-V 32 targets — completing Agents B, C, F, I, and J from the graphics_backend_session_sharing.md plan. Metal session (Agent D) is already done. Each backend must support LegacyNoSession (existing behavior), ManagedShared (retained session), and PerfExclusive (benchmark-only) modes using the BackendSessionHandle/Policy types already created in backend_session.spl.

## Acceptance Criteria
- [x] AC-1: CudaSession class in `gpu/engine2d/cuda_session.spl` — retains primary context, module/kernel cache, device buffer pool; supports retain/release
- [x] AC-2: VulkanSession class in `gpu/engine2d/vulkan_session.spl` — owns instance, device, queue, command pool, pipeline cache, allocator; supports retain/release
- [x] AC-3: CpuSession class in `gpu/engine2d/cpu_session.spl` — CPU feature detection, scalar/SIMD kernel table selection for x86-64 (SSE/AVX), aarch64 (NEON), RISC-V 64/32 (scalar + future RVV)
- [x] AC-4: Engine2D backends (CUDA, Vulkan, CPU) accept session via `init_with_session()` — same pattern as Metal
- [x] AC-5: Legacy `init()` still works for all backends (creates internal LegacyNoSession)
- [x] AC-6: Mode separation tests — PerfExclusive cannot be retained by managed paths; managed sessions reuse state across instances
- [x] AC-7: RISC-V 32/64 and ARM64 compile with scalar CPU fallback and typed "GPU unavailable" diagnostics

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-17
- [x] 2-research (Analyst) — 2026-05-19
- [x] 3-arch (Architect) — 2026-05-19
- [x] 4-spec (QA Lead) — 2026-05-19
- [x] 5-implement (Engineer) — 2026-05-19
- [x] 6-refactor (Tech Lead) — 2026-05-19
- [x] 7-verify (QA) — 2026-05-19
- [x] 8-ship (Release Mgr) — 2026-05-19

## Phase Outputs

### 1-dev
Task: Implement CUDA, Vulkan, and CPU (x86/RISC-V 32/64) backend sessions per the session sharing plan.

Context already established:
- `backend_session.spl` defines BackendSessionMode/Kind/Policy/Handle types
- `metal_session.spl` demonstrates the pattern (retain/release, field extraction)
- `backend_metal.spl` shows `init_with_session()` wiring
- Cranelift JIT already supports x86-64 and aarch64
- CUDA FFI already exists (`cuda_ffi.spl`, 53 rt_cuda_* functions)
- Plan doc: `doc/03_plan/agent_tasks/graphics_backend_session_sharing.md`

Scope: Agents B (CUDA), C (Vulkan), F (CPU SIMD), I (ARM/RV validation), J (mode tests).
Not in scope: Agent E (WebGPU), Agent G (Engine2D API migration beyond init_with_session), Agent H (Web Engine/WM).

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
