<!-- codex-research -->
# Graphics 3D Session Managed Backend Local Research

Date: 2026-05-17
Status: local research note

## Scope

This note extends the existing 2D session-sharing work to 3D rendering, 2D game rendering, 3D game rendering, the web renderer, GUI library, and window manager. It is intentionally a plan/research artifact, not an implementation change.

## Existing Local Surface

- `doc/03_plan/agent_tasks/graphics_backend_session_sharing.md` already defines `LegacyNoSession`, `ManagedShared`, and `PerfExclusive` for 2D backends and covers CUDA, Vulkan, Metal, CPU, WebGPU, web engine, WM, and ARM/RISC-V preparation.
- `src/lib/gc_async_mut/gpu/engine2d/backend_core.spl` and related 2D backend files already point toward probeable region operations, backend diagnostics, strict selection, frame pacing, and readback policy.
- `doc/07_guide/api/webgpu_guide.md` already describes a 3D WebGPU backend direction and extended feature probing.
- `doc/07_guide/api/gpu_api.md` already lists CUDA, Vulkan, Metal, WebGPU, CPU, 2D, and 3D concepts, but it does not yet define persistent session/managed policy as the shared API contract.
- `doc/07_guide/compiler_optimization_plugin.md` defines optimization plugin kinds, provider metadata, lookup strategy, lifecycle, and compatibility rules. It should become the shared home for JIT/backend optimization providers instead of adding local ad hoc caches inside graphics modules.
- `doc/04_architecture/cross_platform_wm.md` and `doc/07_guide/ui_stack_guide.md` define `UISession` as the shared UI state entry point. Graphics backend session handles should remain backend resources referenced by UI/WM backends, not fields cached on `UISession`.

## Current Gap

The 2D plan is strong, but it does not fully spell out the 3D/game-engine shape:

- A common `GraphicsSession` should cover 2D engine, 2D game engine, 3D engine, 3D game engine, web renderer, GUI library, and WM.
- Managed mode needs a stable ownership rule that avoids mixing benchmark-oriented `PerfExclusive` resources with app-managed shared resources.
- 3D needs explicit handling for swapchains/surfaces, render passes, pipeline layout caches, bind/resource groups, shader/JIT specialization, mesh/texture/scene buffers, and present/readback policy.
- Web renderer, GUI, and WM should use the same session capability model instead of each adding backend-specific toggles.
- Persistent optimization state should be shared through the optimization plugin/provider registry, not duplicated in renderer-local JIT caches.

## Pure Simple / C ABI Direction

The public API should be Pure Simple first:

- Stable Simple traits/classes for session policy, capability probe, render passes, command submission, performance counters, and optimization providers.
- No Rust runtime library requirement in the common graphics API.
- Native backend bindings should use a C ABI shim where direct OS/GPU API calls are unavoidable.
- Existing Rust code under `src/compiler_rust/**` may remain compiler/tooling implementation detail, but should not be the required runtime graphics library boundary.

## Risks

- Treating CUDA as a presentation backend would force readback or interop complexity. CUDA should be a compute/render accelerator and interop participant; presentation remains Vulkan, Metal, WebGPU, D3D-family, WM framebuffer, or CPU path.
- Storing backend resources inside `UISession` would couple UI state lifetime to GPU device lifetime and break cross-backend testing.
- Allowing `ManagedShared` and `PerfExclusive` to share device queues, allocators, or caches would invalidate performance measurements and can violate synchronization assumptions.
