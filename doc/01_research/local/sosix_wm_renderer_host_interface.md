<!-- codex-research -->

# SOSIX Refactor Research: WM and Renderer Host Interfaces

**Date:** 2026-08-11

## Decision

WM, GUI, Web, Draw IR, and Engine2D semantics must remain independent of SOSIX. Their host-facing operations should move behind typed SOSIX service capabilities, with asynchronous operations wherever completion is naturally deferred. SOSIX owns host access; it does not become a renderer or absorb transient GPU/render state.

```text
WM / GUI / Web -> DrawIrComposition -> Engine2D
                                      |
                         typed display/input/time/file capabilities
                                      |
                                async SOSIX ops
                                      |
                         hosted OS or SimpleOS service backend
```

## Local evidence

The current compositor tree contains direct host dependencies in several categories:

- `qemu_capture.spl`: raw filesystem probes/read and thread sleep while waiting for QMP output.
- `frame_pacer.spl` and `perf_counters.spl`: raw monotonic time and sleep.
- `wm_gui_window_drawing_evidence.spl` and `hosted_wm_capture_evidence.spl`: raw env/time/file writes.
- `backend_factory.spl`, `compositor_engine2d.spl`, and `host_compositor_bootstrap.spl`: raw environment reads inside selection/bootstrap paths.
- `hosted_input_backend.spl` and `hosted_input_sdl2.spl`: direct winit/SDL event polling and lifecycle calls.
- `hosted_backend*.spl` and `gui_renderer.spl`: direct window, staging-buffer, present, dynamic-library, SDL/winit/Cocoa/Win32 calls.

Portable UI code already points toward the right boundary: `src/lib/common/ui/screen_host.spl` defines host interaction, `input_backend.spl` has one typed `poll_event` ingress, `ui_frame_clock.spl` separates portable timing from the hosted clock, and Draw IR is the canonical semantic rendering payload.

## Boundary classification

| Current dependency | SOSIX target | Async policy |
|---|---|---|
| window create/resize/destroy | `DisplaySessionCapability` control operations | async, with explicit completion |
| frame present/readback | `DisplaySurfaceCapability` | async submit/completion; batching allowed |
| input polling | `InputStreamCapability` | async event stream; nonblocking `try_take` adapter |
| sleep/frame deadline | `TimerCapability` | async deadline operation; no busy spin |
| file evidence/capture | `FileWriteCapability`/`FileReadCapability` | async `write_at`/`read_at`; sync adapter only at CLI boundary |
| QMP/process lifecycle | `ProcessCapability` + IPC/socket capability | async spawn/request/wait with bounded deadline |
| environment selection | immutable `HostConfigurationSnapshot` | captured once at startup; no repeated async lookup in hot frame paths |
| dynamic library/symbol loading | `LibraryCapability` control plane | async/open at startup, then immutable checked dispatch table |
| GPU submission/readback | existing Engine2D/backend capability | retain renderer ownership; expose completion through the shared operation model only |
| Draw IR, layout, scene, raster algorithms | no SOSIX dependency | synchronous/pure unless their own compute scheduler applies |

## Required interfaces

```text
HostDisplayService
    open_session_async
    create_surface_async
    present_async
    readback_async
    resize_async
    close_async

HostInputService
    next_event_async
    try_take_event

HostTimerService
    deadline_async
    monotonic_now

HostConfigurationSnapshot
    backend
    display
    motion
    evidence
```

All asynchronous results use the canonical SOSIX `OperationId`/typed completion/cancellation/deadline model. Backend-specific handles stay private to the service implementation. WM sees typed capabilities, not raw winit/SDL/Cocoa/Win32 IDs.

## Migration order

1. Freeze service traits and configuration snapshot without changing behavior.
2. Move raw environment reads into one startup configuration owner.
3. Move file/QMP evidence I/O to existing file/process facades, then the canonical SOSIX async core.
4. Adapt frame clocks to `HostTimerService`; retain a bounded synchronous compatibility wait only at the outer event-loop boundary.
5. Adapt input backends to publish typed events into one SOSIX-backed event stream.
6. Adapt present/readback to typed async display operations; preserve Draw IR and Engine2D ownership.
7. Move create/resize/destroy/dynlib startup control behind capabilities.
8. Delete backend-local raw host calls after behavior and native-host evidence agree.

## Correctness constraints

- Do not route Draw IR text, layout, rasterization, or GPU atlas/cache state through SOSIX.
- Do not make one host request per pixel, primitive, or input accessor; use frames, batches, and event queues.
- Present ordering is `(surface generation, frame sequence)`; stale completions are rejected.
- Resize invalidates the old surface generation.
- Input preserves source sequence and timestamp; coalescing may apply only to explicitly coalescible motion events.
- Cancellation never converts an accepted present into two completions.
- The synchronous adapter must sleep/wait through notifications, never poll unboundedly.
- Headless and SimpleOS framebuffer backends implement the same traits without pretending to be hosted winit/SDL backends.

## Test implications

Unit tests cover operation state machines, generation/sequence rejection, input ordering/coalescing, configuration snapshot immutability, and cancellation races. Integration tests compare existing and SOSIX adapters against absolute Draw IR/pixel/input oracles. System tests run the production WM path on Linux/Windows/macOS/FreeBSD when available and the six SimpleOS QEMU guest rows, retaining boot, input, present/readback, filesystem listing, and arbitrary program evidence.

Unavailable native renderer hosts remain blocked. TCG/QEMU proves guest correctness, not native Metal/DirectX/Vulkan performance.

