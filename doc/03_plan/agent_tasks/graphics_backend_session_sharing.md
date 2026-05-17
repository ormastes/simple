<!-- codex-design -->
# Graphics Backend Session Sharing Plan

Date: 2026-05-17
Status: candidate plan

## Goal

Add a common session-sharing model for 2D rendering backends while preserving the old no-session API. The design must cover CUDA, Vulkan, Metal, CPU-only, WebGPU/wgpu, the web engine, and the window manager. It must prepare ARM and RISC-V 32/64 targets. Most importantly, performance mode and managed/session mode must not be mixed in a way that creates correctness, lifetime, or benchmarking problems.

## Local Context

Recent code already moved toward a probe/perf architecture:

- `src/lib/gc_async_mut/gpu/engine2d/backend_core.spl` now has `RenderBackendProbe` and `RenderBackendRegionOps` for `fill`, `blit`, `alpha_blend`, `scroll`, and `sync_readback`.
- `src/lib/gc_async_mut/gpu/engine2d/backend_probe.spl` defines typed backend diagnostics.
- `src/lib/gc_async_mut/gpu/engine2d/ffi_dispatch.spl` rejects GLSL by default and separates strict backend selection from fallback.
- `src/lib/gc_async_mut/gpu/engine2d/wm_frame_pacing.spl` adds frame pacing counters and a sleep-based tick helper.
- Existing benchmark fixtures under `test/perf/graphics_2d`, `test/perf/tauri_equiv`, and `test/perf/web_render_chrome` show the current direction: backend proof plus comparative performance.

## Domain Research Summary

- CUDA: the CUDA Driver API has a primary context model. A retained primary context can be shared per device across modules and avoids repeatedly creating contexts. Direct compute render can use PTX kernels and device framebuffer memory; Windows presentation should later use CUDA/D3D interop to avoid readback.
- Vulkan: long-lived state should include instance, physical/logical device, queue family, queues, descriptor/pipeline caches, allocator, and command pools. Command pools are tied to queue families and require synchronization rules, so session sharing must own the pool policy.
- Metal: Apple recommends persistent `MTLDevice` and generally one `MTLCommandQueue` per GPU; pipeline states are expensive and should be reused. Metal resources are tied to one device.
- wgpu/WebGPU: `Device` and `Queue` are the portable session primitives; they should be reused and surfaced as a backend session rather than created per draw call.

Sources:
- CUDA Driver API primary context docs: https://docs.nvidia.com/cuda/archive/12.3.1/cuda-driver-api/group__CUDA__PRIMARY__CTX.html
- Vulkan command buffer/queue docs: https://docs.vulkan.org/spec/latest/chapters/cmdbuffers.html and https://docs.vulkan.org/guide/latest/queues.html
- Apple Metal persistent objects: https://developer.apple.com/library/archive/documentation/3DDrawing/Conceptual/MTLBestPracticesGuide/PersistentObjects.html
- Apple `MTLCommandQueue`: https://developer.apple.com/documentation/metal/mtlcommandqueue
- wgpu docs: https://wgpu.rs/doc/wgpu/index.html

## Core Design

Create a small common module:

```text
src/lib/gc_async_mut/gpu/engine2d/backend_session.spl
src/lib/gc_sync_mut/gpu/engine2d/backend_session.spl
src/lib/nogc_async_mut/gpu/engine2d/backend_session.spl
src/lib/nogc_sync_mut/gpu/engine2d/backend_session.spl
```

The no-GC sync module should own the real low-level FFI/session contract where possible. The GC and async modules should be facades.

### Types

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

### Required API

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

Implementation rule: old no-session APIs internally create a short-lived `LegacyNoSession` session. They must not enter `PerfExclusive` or shared managed caches unless the caller explicitly opts in.

## Two Usage Modes

### Legacy No-Session

Use when:

- compatibility with existing examples/tests matters;
- one-shot smoke tests are enough;
- backend creation overhead should remain visible;
- no cross-window or cross-surface sharing is desired.

Properties:

- creates and destroys backend state per Engine2D instance;
- can fall back if caller uses old fallback APIs;
- cannot claim optimized backend performance;
- cannot reuse command queues, CUDA contexts, Metal queues, or pipeline caches across windows.

### Managed Shared Session

Use when:

- app/window/web engine owns multiple surfaces;
- backend resources should be reused;
- perf claims need warm state;
- WM and web engine need stable frame pacing.

Properties:

- one shared session per backend/device/policy tuple;
- supports shared pipeline/kernel/resource caches;
- session records ownership, thread policy, and lifecycle;
- frame objects own transient command buffers or command encoders;
- can support strict backend mode and typed unavailable diagnostics.

### Perf Exclusive

Use only for benchmarks:

- no fallback;
- no unrelated app/window sharing;
- stable warmup/sample policy;
- explicit counters;
- no managed-mode cache pollution unless the benchmark explicitly measures shared warm caches.

Rule: `PerfExclusive` must not be accepted by normal app APIs without a benchmark/test policy marker. This prevents perf-only assumptions from leaking into production management mode.

## Backend Mapping

### CUDA

Session owns:

- retained primary context or explicit driver context;
- module/PTX cache;
- kernel handle cache;
- device framebuffer allocations;
- optional stream;
- copy/readback buffers;
- future D3D interop handles on Windows.

Legacy no-session wraps the current CUDA backend behavior: allocate, load PTX, launch, sync, readback, free.

Managed shared mode keeps context/module/kernel/cache alive across Engine2D surfaces. Resource ownership must be generation-checked so stale framebuffers cannot be used after release.

### Vulkan

Session owns:

- instance and physical/logical device;
- queue family and queues;
- allocator;
- descriptor set layout and descriptor pools;
- pipeline cache;
- command pools per thread or per frame lane;
- SPIR-V shader modules;
- staging/readback buffers.

Legacy no-session creates enough state for one backend instance. Managed mode must own command-pool synchronization because Vulkan command pools are not freely thread-safe.

### Metal

Session owns:

- `MTLDevice`;
- `MTLCommandQueue`;
- compute pipeline states;
- library/MSL function cache;
- buffers/textures;
- optional drawable/surface bridge.

Legacy no-session can create device/queue/pipelines per backend instance. Managed shared mode reuses `MTLDevice`, command queue, and pipeline states. Resources must never cross devices.

### WebGPU/wgpu

Session owns:

- instance;
- adapter;
- device;
- queue;
- pipeline/shader cache;
- texture/staging resources.

Managed mode is the natural wgpu path. Legacy no-session still creates a short-lived off-screen device path for compatibility.

### CPU Scalar / CPU SIMD

Session owns:

- CPU feature set;
- selected kernel table;
- optional tile/thread pool;
- glyph/text cache;
- benchmark counters.

ARM and RISC-V targets may only get scalar initially. SIMD provider dispatch must be feature-gated and never assume x86 AVX/SSE availability.

## 2D Rendering API Plan

Add session-aware constructors:

```text
Engine2D.create_with_session(width, height, session)
Engine2D.create_managed(width, height, kind, policy)
Engine2D.create_perf(width, height, kind, policy)
```

Keep existing constructors as no-session wrappers.

Add performance interface:

```text
RenderBackendPerf:
  begin_sample(label)
  end_sample(label)
  counters()
  reset_counters()
  backend_mode()
  session_id()
```

`RenderBackendPerf` must be read-only with respect to backend behavior. It can report counters, but it must not change scheduling, caching, fallback, or readback policy. Behavior-changing perf settings belong in `BackendSessionPolicy`.

## Web Engine And WM Plan

Web engine:

- create a `RenderSurfaceSession` for web-rendering surfaces;
- share the backend session with Engine2D where possible;
- track parse/style/layout/paint/upload/present counters separately;
- use explicit readback only in test/pixel-compare mode.

Window manager:

- owns top-level `BackendSessionPolicy` for app/window groups;
- child windows retain the session and get separate frame resources;
- dirty-rect, present batching, and frame pacing live in WM/session frame stats;
- WM must never force `PerfExclusive` for normal windows.

Session relationship:

```text
AppSession
  -> BackendSession
     -> WindowSurfaceSession
        -> Engine2D frame / Web frame
```

## ARM And RISC-V 32/64 Preparation

Targets:

- ARM32: scalar first; optional NEON if target feature exists.
- ARM64: scalar plus NEON where available.
- RV32: scalar first; future vector extension optional.
- RV64: scalar first; future vector extension optional.

Design rules:

- keep `target_arch` and `target_bits` in `BackendSessionHandle`;
- session policy must record `cpu_features`;
- CPU SIMD provider must degrade to scalar with typed diagnostics;
- GPU backends are unavailable unless target OS/runtime has the driver API;
- baremetal/framebuffer paths remain separate from CUDA/Vulkan/Metal sessions.

Common module should avoid pointer-width assumptions. Handles use opaque `i64` IDs at the Simple boundary, but native runtime tables must validate target pointer width and ownership internally.

## Preventing Perf/Managed Mode Mixing

Hard rules:

1. `BackendSessionMode` is immutable after session creation.
2. `PerfExclusive` sessions cannot be retained by app/window manager production paths.
3. Managed sessions cannot silently enable benchmark-only counters that alter scheduling.
4. Legacy no-session cannot publish performance parity numbers except cold-start/no-session benchmarks.
5. A frame created from one session cannot be submitted to another session.
6. Readback policy is explicit: `allow_readback` must be true for pixel comparison tests.
7. Fallback policy is explicit: `allow_fallback=false` for perf and backend proof.
8. Cache pollution is tracked: perf reports must say cold, warm-managed, or perf-exclusive.

## Minimizing API Differences

Use a single high-level call shape:

```text
Engine2D.create(width, height)                         # old path
Engine2D.create_managed(width, height, kind, policy)   # shared session
Engine2D.create_with_session(width, height, session)   # explicit session
```

Every backend implements the same region operations:

- `fill`
- `blit`
- `alpha_blend`
- `scroll`
- `sync_readback`

Backend-specific differences stay behind `BackendSessionPolicy` and diagnostics:

- CUDA: PTX/module/context/stream.
- Vulkan: SPIR-V/queue/command pool.
- Metal: MSL/device/command queue.
- WebGPU: WGSL/device/queue.
- CPU: scalar/SIMD kernel table.

## Agent Work Breakdown

### Agent A: Session Contract

Owns:

- `backend_session.spl` in no-GC sync and facades.

Tasks:

- define session mode/kind/policy/handle/error;
- add create/retain/release/probe APIs;
- add generation checks and typed errors.

### Agent B: CUDA Session

Owns CUDA backend and FFI.

Tasks:

- retain/share primary context;
- cache PTX modules and kernel handles;
- support legacy no-session wrapper;
- add Windows note for future CUDA/D3D interop.

### Agent C: Vulkan Session

Owns Vulkan backend/session integration.

Tasks:

- session owns device, queue, allocator, descriptor/pipeline caches, command pools;
- enforce per-thread/per-frame command pool policy;
- keep SPIR-V-only production path.

### Agent D: Metal Session

Owns Metal backend/session integration.

Tasks:

- session owns `MTLDevice`, command queue, pipeline states, library cache;
- macOS-only verification;
- no resource crossing between devices.

### Agent E: WebGPU/wgpu Session

Owns WebGPU hosted/native path.

Tasks:

- session owns adapter/device/queue;
- add explicit real/stub diagnostics;
- integrate web engine surfaces.

### Agent F: CPU SIMD Session

Owns CPU kernel table and optimization metadata.

Tasks:

- expose scalar/SIMD provider selection;
- target-gate x86, ARM NEON, future RISC-V vector;
- ensure scalar fallback is always correct.

### Agent G: Engine2D API Migration

Owns Engine2D constructors and perf interface.

Tasks:

- add session-aware constructors;
- keep old constructors as wrappers;
- add read-only perf counters;
- prevent perf policy mutation through counters.

### Agent H: Web Engine And WM

Owns web renderer/WM session adoption.

Tasks:

- add `RenderSurfaceSession`;
- retain backend session per window;
- add frame stats and dirty-rect propagation;
- forbid `PerfExclusive` for production windows.

### Agent I: ARM/RISC-V Validation

Owns target matrix and compile checks.

Tasks:

- add ARM32/ARM64/RV32/RV64 scalar session checks;
- add feature-gated NEON/RVV planning tests;
- verify no pointer-width assumptions in Simple-visible handles.

### Agent J: Mode Separation Tests

Owns policy/system tests.

Tasks:

- test legacy no-session remains compatible;
- test managed session sharing reuses state;
- test perf-exclusive cannot be retained by WM;
- test strict no-fallback and explicit readback policy.

## Acceptance Criteria

- Old no-session Engine2D examples still pass.
- Managed shared sessions work for CPU and at least one GPU backend.
- CUDA, Vulkan, Metal plans map to their native persistent-state concepts.
- Web engine and WM can retain a backend session without entering perf-exclusive mode.
- Perf interface reports counters without changing behavior.
- ARM/RISC-V 32/64 paths compile with scalar fallback and typed unavailable GPU diagnostics.
- Tests prove perf mode and managed mode cannot be accidentally mixed.

