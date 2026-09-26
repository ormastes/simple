# SOSIX route manifest v1: hosted display, input, and GPU queue

Status: **partial RU-001 census**, source inspected at `3374a69ce09` on
2026-09-26. These are current routes, not proof of live GPU execution, Cocoa
present completion, SimpleOS parity, or RU-051 qualification.

## Route keys

| Key | Profile and current owner |
|---|---|
| D | Hosted display: SOSIX display state, toolkit adapter, native window/layer provider |
| I | Hosted input: toolkit event owner, `HostInputEvent`, SOSIX input stream |
| Q | Engine2D compatibility queue: Simple projection and native bookkeeping |
| O | SimpleOS display/input device owners under `src/os/`; parity with D/I remains open |

## Classified routes

| Symbol and source | Signature; caller → owner → route | Disposition and evidence gap |
|---|---|---|
| `sosix_display_request_create`, [`service_contract.spl`](../../../../src/os/sosix/host/service_contract.spl) | Typed request validation; hosted adapters → SOSIX host contract → D | Surface capability, generation, frame sequence, buffer, and deadline form one request identity. Validation is not presentation. |
| `sosix_display_surface_submit/complete`, [`display_surface_state.spl`](../../../../src/os/sosix/host/display_surface_state.spl) | `(SosixDisplaySurfaceState, SosixDisplayRequest/CompletionKey) -> SosixDisplaySurfaceTransition`; adapters → bounded generation/sequence owner → D | Submit increments in-flight count. Completion requires oldest sequence and matching generation. Bind native failure and observed completion to this owner. |
| `sosix_sdl2_submit_composition`, [`sdl2_display_adapter.spl`](../../../../src/os/compositor/host_services/sdl2_display_adapter.spl) | `(Engine2dCompositorBackend, HostedSdl2Backend, SosixDisplaySurfaceState, SosixDisplayRequest, DrawIrComposition) -> SosixSdl2PresentSubmission`; Engine2D raster → SDL2 present → D | Synchronous `present_checked` result precedes SOSIX completion observation. Verify retained state on rejection after submission. |
| `sosix_cocoa_submit_composition`, [`cocoa_display_adapter.spl`](../../../../src/os/compositor/host_services/cocoa_display_adapter.spl) | `(SosixHostConfigurationSnapshot, Engine2dCompositorBackend, HostedCocoaBackend, SosixDisplaySurfaceState, SosixDisplayRequest, DrawIrComposition) -> SosixCocoaPresentSubmission`; Engine2D raster → Cocoa layer → D | Returns a pending fence. This route has no observed native present completion. |
| `HostedCocoaBackend.blit_pixels`, [`hosted_backend_cocoa.spl`](../../../../src/os/compositor/hosted_backend_cocoa.spl) | `(i32,i32,i32,i32,[u32]) -> ()`; Cocoa adapter → per-pixel `put_pixel`/`fill_rect` → native Cocoa layer → D | Full-frame transfer makes one native call per pixel. Add a checked bulk transfer before the no-per-primitive host-request and latency gates. |
| `rt_cocoa_layer_present`, [`hosted_cocoa.c`](../../../../src/runtime/hosted_cocoa.c) | `(i64,i64) -> bool`; Cocoa backend → native window/layer → D | `HostedCocoaBackend.present()` discards the bool, so the adapter cannot distinguish native rejection from a pending frame. |
| `Sdl2InputBackend.poll_event`, [`hosted_input_sdl2.spl`](../../../../src/os/compositor/hosted_input_sdl2.spl) | `() -> HostInputEvent?`; SDL2 event queue → canonical input event → I | Native aliases come from one `window_abi` owner. Preserve key normalization and live-window availability. |
| `HostedInputBackend.poll_event`, [`hosted_input_backend.spl`](../../../../src/os/compositor/hosted_input_backend.spl) | `() -> HostInputEvent?`; winit event-loop externs → canonical input event → I | Confirm native/interpreter tuple ABI and event release; the shared trait alone does not prove SDL2 parity. |
| `sosix_host_input_publish`, [`host_input_producer_adapter.spl`](../../../../src/os/sosix/host/host_input_producer_adapter.spl) | `(SosixInputStreamState, HostInputEvent, u64) -> SosixInputStreamTransition`; host callback → typed adapter → I | The adapter does not poll. Event acquisition and monotonic timestamp belong to the host loop. |
| `sosix_input_stream_publish`, [`input_stream_state.spl`](../../../../src/os/sosix/host/input_stream_state.spl) | `(SosixInputStreamState, SosixHostInputEvent) -> SosixInputStreamTransition`; adapter → bounded stream → I | Checks sequence, time, backpressure, and motion-only coalescing. Native loss/resync remains unproven. |
| `engine2d_host_gpu_runtime_emit_packet/drain`, [`host_gpu_event_queue.spl`](../../../../src/lib/gc_async_mut/gpu/engine2d/host_gpu_event_queue.spl) | Queue packet/count adapters → `rt_host_gpu_queue_*` → Q | Compatibility transport; packet acceptance and completed counts are not GPU execution evidence. |
| `rt_host_gpu_active_backend_handle` / `rt_host_gpu_queue_complete_packet`, [`runtime_native.c`](../../../../src/runtime/runtime_native.c) | `() -> i64` returns 0; private completion bookkeeping over metadata → Q | Core runtime binds no active GPU backend. The completion path does not submit a device program or read back physical output. |

## Next gates

1. RU-051: add one checked bulk frame transfer and result-bearing present path
   for a real hosted provider. Retain surface generation, frame sequence, and
   buffer lease through observed completion or failure.
2. RU-050: connect toolkit producers to one bounded SOSIX input stream owner
   with loss/resync and stale-surface controls. Keep host event acquisition in
   the toolkit owner.
3. RU-061/RU-062: authenticate a device program and task owner, submit real
   GPU work, independently check readback, and retire a physical fence. Queue
   counts cannot satisfy this gate.
4. RU-001 remains globally open: other renderer backends, platform device
   imports, network, and remaining host effects still need classified rows.
