<!-- codex-design -->
# Graphics 3D Session Managed Backend Detail Design

Date: 2026-05-17
Status: candidate detail design

## Common API Sketch

```text
GraphicsSession.create(policy) -> Result<GraphicsSession, GraphicsError>
GraphicsSession.retain() -> Result<GraphicsSession, GraphicsError>
GraphicsSession.release() -> Result<(), GraphicsError>
GraphicsSession.capabilities() -> GraphicsCapabilities
GraphicsSession.begin_frame(surface) -> Result<GraphicsFrame, GraphicsError>
GraphicsSession.submit(commands) -> Result<SubmitReceipt, GraphicsError>
GraphicsSession.end_frame(frame) -> Result<FrameStats, GraphicsError>
GraphicsSession.readback(frame, region) -> Result<PixelBuffer, GraphicsError>
```

Legacy no-session wrappers remain:

```text
Engine2D.create(width, height)
Game2D.create(width, height)
Engine3D.create(width, height)
Game3D.create(width, height)
WebRenderer.create(surface)
GuiApp.create()
WindowManager.create()
```

Each wrapper internally creates `LegacyNoSession` unless passed an explicit `GraphicsSession`.

## Persistent API Objects

| Object | Persistent key | Invalidated by |
|--------|----------------|----------------|
| Device/session | backend kind + adapter id + target arch | device loss, driver reset |
| Queue/command pool | session id + queue policy | mode switch, queue-family change |
| Allocator/heap | session id + memory policy | memory pressure, device loss |
| Shader/kernel cache | provider id + backend + target + policy hash | source change, feature change |
| Pipeline cache | backend + render pass format + shader key | surface format change |
| Perf counters | session id + mode | session end |

## Managed vs Perf Separation

`ManagedShared` and `PerfExclusive` are separate ownership domains.

- Managed sessions may share immutable compiled shader blobs and read-only capability tables.
- Perf sessions may read static capability tables, but must own queues, allocators, command pools, command buffers, timing counters, mutable pipeline caches, and warmup state.
- Cross-mode object use must return a typed error such as `GraphicsError.ModeConflict`.

## 3D Engine Plan

- Add common scene resource abstractions: mesh buffer, index buffer, texture, material, bind group, render pass, camera, and scene graph node.
- Backend adapters translate these objects to Vulkan descriptors/pipelines, Metal resources/pipeline states, WebGPU bind groups/pipelines, CUDA kernels/intermediate buffers, or CPU SIMD loops.
- CUDA 3D path targets compute raster/particle/physics/denoise/postprocess kernels first; presentation must go through interop or CPU readback policy.
- CPU path is the reference backend and must preserve deterministic output for tests.

## 3D Game Engine Plan

- Build over the 3D engine with frame lifecycle, asset streaming, animation update, physics handoff, input snapshot, and frame pacing.
- Session policy is selected at game/app startup and may be inherited by tools, editor windows, and replay capture.
- Replay and benchmark modes should use `PerfExclusive` to isolate warmup and counters.

## 2D/Game/Web/GUI/WM Adoption

- 2D engine adopts `GraphicsSession` as the generic form of the current backend-session plan.
- 2D game engine uses the same session for sprites, tile maps, particles, and frame pacing.
- Web renderer maps layout paint fragments to 2D commands and WebGPU/3D commands when CSS transforms, canvas, or GPU effects require it.
- GUI library maps widgets to retained paint commands and receives a session from the app shell or WM.
- WM owns compositor sessions and can pass child sessions/capabilities to hosted GUI/web surfaces without exposing raw backend handles.

## Optimization/JIT Sharing

- Add graphics providers to the optimization plugin metadata model:
  - `simple.opt.graphics.shader_specialization`
  - `simple.opt.graphics.pipeline_cache`
  - `simple.opt.graphics.cpu_simd_vectorization`
  - `simple.opt.graphics.cuda_kernel_specialization`
  - `simple.opt.graphics.webgpu_layout_specialization`
- Provider outputs are persistent facts: shader variant keys, SIMD width facts, bind layout compatibility, memory alignment, and backend feature flags.
- JIT-generated code uses the shared object mapper/icache rules from the glossary loader/JIT section and never creates a separate executable-memory policy.

## ARM/RISC-V Design

- Capability records include `arch_family`, `bits`, `simd_kind`, `vector_bits`, `cache_line_bytes`, `atomic_width`, `icache_flush_required`, and `unaligned_access_policy`.
- ARM32/ARM64 and RISC-V32/RISC-V64 start with CPU and WebGPU/Vulkan where available.
- JIT paths must keep architecture-specific executable-memory and icache behavior behind the shared mapper/provider layer.

## Verification Plan

- Unit tests for mode conflict errors.
- Session lifecycle tests for retain/release, device-loss simulation, and legacy wrapper behavior.
- Golden image tests on CPU reference backend for 2D/3D small scenes.
- Perf harness tests that prove `PerfExclusive` counters exclude managed warmup.
- Cross-surface tests where 2D, 2D game, 3D, web renderer, GUI, and WM all accept the same session policy object.
