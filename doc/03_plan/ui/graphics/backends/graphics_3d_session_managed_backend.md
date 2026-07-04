<!-- codex-design -->
# Agent Plan: Graphics 3D Session Managed Backend

Date: 2026-05-17
Status: candidate implementation plan

> Status: COMPLETE — all phases shipped. Session types (phase 5) via .spipe/gfx-3d-session-backend 2026-05-17; web/GUI/WM handoff, optimization provider integration, and verification (phases 6-8) via .spipe/graphics-3d-session-managed-backend 2026-05-18. 20 spec tests passing.

## Objective

Extend the 2D backend session-sharing plan into a common graphics session architecture for 2D, 2D game, 3D, 3D game, web renderer, GUI library, and WM. Keep Pure Simple APIs first, use C ABI shims for native GPU calls, avoid adding Rust runtime-library coupling, and share JIT/backend optimization through the optimization plugin system.

## Work Breakdown

1. Common API agent
   - Owns `GraphicsSession`, `GraphicsSessionPolicy`, capability records, mode conflict errors, and old no-session wrappers.
   - Must preserve `LegacyNoSession` behavior.

2. 2D/2D-game adoption agent
   - Maps existing engine2d backend session design to generic `GraphicsSession`.
   - Adds sprite/tile/particle session entry points for 2D game use.

3. 3D/3D-game agent
   - Designs scene resources, render passes, material/bind layout, frame lifecycle, and game-loop integration.
   - Keeps CUDA as compute/interop unless a presentation backend is explicitly configured.

4. Web/GUI/WM agent
   - Routes web renderer, GUI library, and WM through the same session policy.
   - Ensures `UISession` stores UI state only and does not own raw GPU backend handles.

5. Backend adapter agent
   - Implements CPU, Vulkan, CUDA, Metal, and WebGPU adapters behind Pure Simple traits.
   - Uses C ABI shims for native GPU APIs.

6. Optimization/JIT agent
   - Adds graphics optimization providers to the Simple Optimization Plugin registry.
   - Shares provider facts with compiler/JIT/backend lowering.
   - Keeps `ManagedShared` and `PerfExclusive` optimization state separate.

7. Architecture verification agent
   - Adds mode-conflict tests, backend capability tests, CPU golden rendering tests, and perf-counter isolation checks.

## Sequencing

1. Land common types and capability records.
2. Adapt old no-session constructors to call `LegacyNoSession`.
3. Add managed/perf policy checks before backend-specific implementation.
4. Port 2D backend to generic session.
5. Add 3D resource and render-pass skeletons.
6. Integrate web/GUI/WM session policy handoff.
7. Register optimization providers and persistent keys.
8. Add verification and perf comparison fixtures.

## Done Criteria

- All surface families accept a session policy and can still run without one.
- `ManagedShared` and `PerfExclusive` cannot accidentally share mutable resources.
- CPU-only backend passes the same API and spec tests.
- CUDA/Vulkan/Metal/WebGPU adapters report capabilities through one structure.
- Optimization/JIT provider state is persistent and keyed by backend/session policy.
- Docs and specs trace every `REQ-GFX-*` requirement.

---

## Merged from graphics_backend_session_sharing

### Session Types

```text
BackendSessionMode:
  LegacyNoSession
  ManagedShared
  PerfExclusive

BackendSessionKind:
  Cpu
  Cuda
  Vulkan
  Metal
  WebGpu

BackendSessionPolicy:
  mode
  allow_fallback
  strict_backend
  allow_readback
  allow_interop_present
  thread_policy
  queue_policy
  allocator_policy
  perf_counters_enabled

BackendSessionHandle:
  id
  kind
  mode
  device_name
  api_name
  target_arch
  target_bits
  owner_thread_id
  generation
```

### Required Session API

```text
backend_session_create(kind, policy) -> Result<BackendSessionHandle, BackendSessionError>
backend_session_retain(handle) -> Result<BackendSessionHandle, BackendSessionError>
backend_session_release(handle) -> Result<(), BackendSessionError>
backend_session_probe(handle) -> BackendProbeResult
backend_session_begin_frame(handle, width, height) -> Result<BackendFrame, BackendSessionError>
backend_session_end_frame(frame) -> Result<BackendFrameStats, BackendSessionError>
backend_session_sync_readback(frame) -> Result<[u8], BackendSessionError>
```

### Old API Preservation

Existing calls remain supported:

```text
Engine2D.create(width, height)
Engine2D.create_with_backend(width, height, "cuda")
backend.init(width, height)
backend.present()
backend.read_pixels()
```

Old no-session APIs internally create a short-lived `LegacyNoSession` session. They must not enter `PerfExclusive` or shared managed caches unless the caller explicitly opts in.

### Engine2D Session-Aware Constructors

```text
Engine2D.create_with_session(width, height, session)
Engine2D.create_managed(width, height, kind, policy)
Engine2D.create_perf(width, height, kind, policy)
```

Read-only perf interface (must not alter scheduling or caching):

```text
RenderBackendPerf:
  begin_sample(label)
  end_sample(label)
  counters()
  reset_counters()
  backend_mode()
  session_id()
```

### Backend Ownership Details

**CUDA:** session owns retained primary context or explicit driver context, module/PTX cache, kernel handle cache, device framebuffer allocations, optional stream, copy/readback buffers, future D3D interop handles on Windows.

**Vulkan:** session owns instance, physical/logical device, queue family and queues, allocator, descriptor set layout and pools, pipeline cache, command pools per thread or frame lane, SPIR-V shader modules, staging/readback buffers. Command pools require per-thread/per-frame synchronization policy.

**Metal:** session owns `MTLDevice`, `MTLCommandQueue`, compute pipeline states, library/MSL function cache, buffers/textures, optional drawable/surface bridge. Resources must never cross devices.

**WebGPU/wgpu:** session owns instance, adapter, device, queue, pipeline/shader cache, texture/staging resources. Managed mode is the natural wgpu path.

**CPU Scalar/SIMD:** session owns CPU feature set, selected kernel table, optional tile/thread pool, glyph/text cache, benchmark counters. SIMD provider dispatch must be feature-gated and never assume x86 AVX/SSE availability.

### Web Engine And WM Session Hierarchy

Web engine creates a `RenderSurfaceSession` for web-rendering surfaces, shares the backend session with Engine2D where possible, tracks parse/style/layout/paint/upload/present counters separately, and uses explicit readback only in test/pixel-compare mode.

Window manager owns the top-level `BackendSessionPolicy` for app/window groups. Child windows retain the session and get separate frame resources. Dirty-rect, present batching, and frame pacing live in WM/session frame stats. WM must never force `PerfExclusive` for normal windows.

```text
AppSession
  -> BackendSession
     -> WindowSurfaceSession
        -> Engine2D frame / Web frame
```

### ARM And RISC-V 32/64 Preparation

Targets: ARM32 (scalar first, optional NEON), ARM64 (scalar + NEON), RV32 (scalar first, future RVV), RV64 (scalar first, future RVV).

- Keep `target_arch` and `target_bits` in `BackendSessionHandle`.
- Session policy must record `cpu_features`.
- CPU SIMD provider must degrade to scalar with typed diagnostics.
- GPU backends unavailable unless target OS/runtime has the driver API.
- Baremetal/framebuffer paths remain separate from CUDA/Vulkan/Metal sessions.
- Handles use opaque `i64` IDs at the Simple boundary; native runtime tables must validate target pointer width internally.

### Perf/Managed Mode Hard Rules

1. `BackendSessionMode` is immutable after session creation.
2. `PerfExclusive` sessions cannot be retained by app/window manager production paths.
3. Managed sessions cannot silently enable benchmark-only counters that alter scheduling.
4. Legacy no-session cannot publish performance parity numbers except cold-start/no-session benchmarks.
5. A frame created from one session cannot be submitted to another session.
6. Readback policy is explicit: `allow_readback` must be true for pixel comparison tests.
7. Fallback policy is explicit: `allow_fallback=false` for perf and backend proof.
8. Cache pollution is tracked: perf reports must say cold, warm-managed, or perf-exclusive.

### Extended Acceptance Criteria

- Old no-session Engine2D examples still pass.
- Managed shared sessions work for CPU and at least one GPU backend.
- CUDA, Vulkan, Metal plans map to their native persistent-state concepts.
- Web engine and WM can retain a backend session without entering perf-exclusive mode.
- Perf interface reports counters without changing behavior.
- ARM/RISC-V 32/64 paths compile with scalar fallback and typed unavailable GPU diagnostics.
- Tests prove perf mode and managed mode cannot be accidentally mixed.

## Refactoring Alignment (2026-06-12)

Per `doc/03_plan/ui/graphics/engine/game_engine_2d3d_unification_plan_2026-06-12.md`
(P1 unified surface), main refactoring executed by a separate agent:

- A managed 3D session's output frame becomes a `CompositeLayer` (z-index 0 by
  default) in the compositor `LayerTree`, composited with 2D/GUI layers on the
  shared `gpu_surface` — sessions do not own the swapchain alone.
- 2D and 3D layers do not share a depth buffer; world-space 2D uses
  render-to-texture on a mesh inside the 3D session.
- Session invariants above are unchanged by the refactor — in particular
  frame-to-session binding (rule 5) and explicit readback/fallback policy
  (rules 6-7) also govern compositor blits.
- Camera `render_order` lives in engine components, not in the session layer.
