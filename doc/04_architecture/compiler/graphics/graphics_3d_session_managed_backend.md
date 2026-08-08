<!-- codex-design -->
# Graphics 3D Session Managed Backend Architecture

Date: 2026-05-17
Status: candidate architecture

## Goal

Define one persistent graphics backend architecture for 2D, 2D game, 3D, 3D game, web renderer, GUI library, and WM surfaces. The architecture preserves legacy no-session APIs while adding explicit `Session`, `ManagedShared`, and `PerfExclusive` modes.

## Requirements Trace

- REQ-GFX-001: Common backend session API covers CPU, CUDA, Vulkan, Metal, WebGPU, and future platform backends.
- REQ-GFX-002: Legacy no-session APIs remain available and internally map to `LegacyNoSession`.
- REQ-GFX-003: Managed shared mode and perf-exclusive mode cannot share mutable queues, allocators, command pools, or timing counters.
- REQ-GFX-004: 2D, 2D game, 3D, 3D game, web renderer, GUI, and WM use the same capability/probe/session policy model.
- REQ-GFX-005: Optimization/JIT metadata is persistent through a shared optimization provider API.
- REQ-GFX-006: Pure Simple API is the default; native GPU bindings use C ABI shims where required and avoid adding a Rust runtime-library dependency.
- REQ-GFX-007: ARM/RISC-V 32/64 and CPU-only backends are represented in the same capability model.

## Layering

```text
app/game/web/gui/wm
  -> graphics facade: 2d, 2d_game, 3d, 3d_game, web_renderer
  -> common graphics session API
  -> optimization provider registry
  -> backend adapters: cpu, cuda, vulkan, metal, webgpu
  -> Pure Simple implementation + C ABI native shims
```

The facade layer owns domain vocabulary such as sprites, scenes, windows, DOM paint fragments, and game worlds. The common session API owns backend lifetime, policy, probes, synchronization, performance counters, and command submission.

## Session Model

`GraphicsSession` is the common handle. Specialized APIs may wrap it, but must not create separate lifetime systems.

```text
GraphicsSessionMode:
  LegacyNoSession
  ManagedShared
  PerfExclusive

GraphicsBackendKind:
  Cpu
  Cuda
  Vulkan
  Metal
  WebGpu

GraphicsSessionPolicy:
  mode
  backend_kind
  surface_policy
  queue_policy
  allocator_policy
  synchronization_policy
  readback_policy
  interop_policy
  optimization_policy
  target_arch
  target_bits
```

Mode rules:

- `LegacyNoSession`: compatibility wrapper. Creates short-lived resources and reports creation cost in counters.
- `ManagedShared`: app/UI/game session. May retain devices, queues, allocators, shader caches, pipeline caches, and optimization providers across frames/windows.
- `PerfExclusive`: benchmark or profiler mode. Uses isolated resources and rejects managed cache borrowing.

## Backend Responsibilities

| Backend | Role | Present path |
|---------|------|--------------|
| CPU | Reference, fallback, SIMD path | WM framebuffer, image buffer, web canvas upload |
| CUDA | Compute/render accelerator, interop participant | Vulkan/D3D/CPU interop, no standalone window present |
| Vulkan | Native graphics/compute/session backend | Vulkan surface/swapchain or external handle |
| Metal | Apple graphics/compute/session backend | Metal layer/surface |
| WebGPU | Browser/native portable backend | Browser canvas, native WebGPU surface |
| Qualcomm | Adreno profile over Vulkan | Vulkan surface/swapchain where driver exists |

## Surface Consumers

All consumers receive either a session or an explicit no-session builder:

- 2D engine: region ops, text, images, scroll, blit, alpha, readback.
- 2D game engine: sprites, tile maps, particles, frame pacing, input-coupled present.
- 3D engine: meshes, scene graph, materials, render passes, resource bindings.
- 3D game engine: world/scene update, animation, physics handoff, streaming assets.
- Web renderer: DOM/layout paint fragments to 2D/3D commands; WebGPU when available.
- GUI library: widget tree raster/vector commands; shared session per app or window group.
- WM: compositor surfaces, window textures, damage regions, present pacing.

## Optimization Provider Integration

Graphics JIT and backend optimization must use the Simple Optimization Plugin provider model:

- Persistent providers are keyed by provider id, target triple, backend kind, session mode, and policy hash.
- Shader/kernel/pipeline specialization facts are produced by backend-metadata providers.
- Renderer-local caches may store handles, but provider metadata and invalidation live in the shared optimization registry.
- `PerfExclusive` gets a private provider instance or a frozen snapshot so measurements are not affected by managed sessions.

## Architecture Guardrails

- Do not store backend device handles directly on `UISession`.
- Do not let a `PerfExclusive` session borrow mutable `ManagedShared` queues, allocators, command pools, pipeline caches, or counters.
- Do not require Rust runtime libraries for graphics backends. Use Pure Simple API and C ABI shims for native GPU calls.
- Do not make CUDA the only render path on Windows; use interop with a presentation backend when direct display is needed.
- Do not hide readback. Every CPU readback path must be visible in counters.
- Do not route Qualcomm through Metal. Qualcomm ARM64/ARM32 preparation uses Vulkan/WebGPU/CPU capability records.
- Do not create a separate ARM mixed JIT runtime. Use one mixed facade over explicit ARM64 and ARM32 JIT handles.
