<!-- codex-architecture -->
# Simple UI, GUI, Web, and 2D Stack Architecture

Status: draft-v3 (2026-06-15)
Owners: `src/app/ui.web`, `src/app/ui.electron`, `src/lib/common/ui`,
`src/lib/gc_async_mut/gpu/browser_engine`,
`src/lib/gc_async_mut/gpu/engine2d`, `src/lib/nogc_async_mut/gpu/engine2d`,
`src/lib/nogc_sync_mut/gpu/engine2d`

Related:
- `doc/04_architecture/ui/ui_web_protocol.md`
- `doc/04_architecture/ui/engine_2d.md`
- `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- `doc/04_architecture/compiler/graphics/gui_layer_contract.md`
- `doc/05_design/compiler/graphics/accelerated_shared_ui_backend_architecture.md`

## Purpose

This document is the canonical stack-level architecture for Simple UI surfaces:
TUI, GUI, web, host wrappers, render IR, Engine2D, and accelerated draw
execution. It records the next refactoring direction from the current renderer
shape: keep UI semantics and event ownership in Simple, introduce a typed
render/draw IR boundary, and allow a render optimization plugin to accelerate
draw batches without taking over GUI policy.

## Target Stack

The stack is not a strict "Electron/Tauri under Simple" chain. Tauri,
Electron, Chrome, browser windows, and native host windows are shells. They
transport pixels, patches, input, and host commands around a Simple-owned UI
and renderer contract.

```
Simple code
  |
  v
Simple UI API
  |-------------------------------|
  v                               v
Simple TUI                    Simple GUI API
                                  |
                                  v
                         Pure Simple GUI event handler
                         event callback ids, focus,
                         command routing, async dispatch
                                  |
                                  v
                         Pure Simple GUI AST layer
                         widgets, layout intent,
                         style intent, accessibility
                                  |
                                  v
                         Simple Web API / adapter
                         snapshots, patches, commands,
                         host-safe transport
                                  |
             -------------------------------------------
             |                                         |
             v                                         v
      Optional HTML text/parser path             Direct typed render path
      html-text -> html parser -> html-ast       GUI AST -> WebRender IR
      source=html_ast, css identity             source=gui_ast, style rev
             |                                         |
             --------------------+--------------------|
                                  v
                         Render IR transfer
                         style, surfaces, text runs,
                         images, dirty regions,
                         screen config, callback ids
                                  |
                                  v
                              Draw IR
                         single/composed batches,
                         window/pane composition,
                         callback id locality,
                         source/style provenance,
                         semantic font-family only
                                  |
                                  v
                           Simple 2D API
                                  |
                                  v
                    Render Optimization Plugin
                    capability probe, cost model,
                    batch selection, cache keys,
                    fallback reason reporting
                                  |
             ----------------------------------------------
             |                                            |
             v                                            v
      Drawing backend lane                      Processing backend lane
      primitive draw, framebuffer,              compute kernels, generated
      present, readback                         artifacts, filters, SIMD/GPU
      CPU/SIMD oracle, Vulkan/Metal             offload, sync evidence
             |                                            |
             ---------------- shared Engine2D API ---------|
                                  |
                                  v
                         Draw processing
                         raster, glyph masks,
                         gradients, alpha blend,
                         compositing, scroll/copy
                                  |
                                  v
                         Primitive draw layer
                         rects, images, text,
                         paths, framebuffer writes
                                  |
                                  v
                         Framebuffer / texture
                                  |
                                  v
                         Present to host window
```

Event and redraw flow:

```
Host window / input
  |
  v
event callback id
  |
  v
Pure Simple GUI event dispatcher
  |
  v
Simple CPU / async task state update
  |
  v
changed GUI AST + dirty region truth
  |
  v
WebRender IR / Draw IR batch
  |
  v
Render Optimization Plugin
  |
  v
CPU or GPU draw execution
```

## Ownership Rules

Web semantic/layout and GUI scene owners preserve text family/style as Draw IR
computed-style metadata. Draw IR never owns font bytes, glyphs, atlases, or
caches. A family becomes executable only after web layout and Engine2D paint
bind to the same provider/`FontRenderer` metric identity; paint-only selection
is forbidden because it diverges from line wrapping. Until then the legacy
bitmap behavior stays active. SimpleOS must obtain the same pinned bytes through
a canonical immutable image-data manifest rather than a host-only path or an
app-private font bundle.

Simple owns:

- widget tree and GUI AST;
- event callback ids, focus, command routing, and state transitions;
- layout policy and accessibility state;
- dirty-region truth and cache invalidation decisions;
- typed `WebRender IR` and `Draw IR` contracts;
- CPU fallback behavior and conformance tests.

The render optimization plugin owns:

- capability probing and backend selection;
- cost estimation for CPU versus GPU execution;
- draw-batch compilation or kernel selection;
- execution, synchronization, and readback;
- explicit fallback reports when a preferred backend cannot run.

Shell wrappers own:

- process launch, window creation, webview/browser embedding, and host IPC;
- forwarding input to Simple callback ids;
- presenting textures, framebuffers, or browser patches supplied by Simple;
- host-native commands only through the Simple UI protocol.

## Boundaries

### Simple UI and TUI

`Simple UI API` is the common entry point. The TUI path may render directly to
terminal surfaces, but it should share command names, focus semantics, and event
ids with GUI where practical. TUI code must not depend on GUI wrappers or GPU
availability.

The low-dependency UI/dynSMF lane makes this boundary executable:
`app.ui.tui` and the TUI compatibility renderer must stay free of GUI, web,
TUI-web, browser, HTML renderer, and CSS implementation imports. The exact
module-prefix dependency gate in `src/app/ui/dependency_closure_gate.spl`
checks that `app.ui.tui` does not accidentally match similarly named modules
such as `app.ui.tui_web`.

### Renderer Capability Boundary

Renderer implementation capabilities live outside the base UI/TUI closure.
`src/app/ui.render/capability.spl` declares implementation-free metadata for
`html_renderer`, `css_provider`, and `tui_renderer`. HTML-capable widgets and
host web adapters import `app.ui.render.html_widgets` directly; the legacy
`app.ui.render.widgets` module remains a TUI-only compatibility wrapper.

CSS is component-scoped at the adapter edge. Web-capable adapters call
`css_for_components([...])` from `app.ui.render.css` to request only the style
payloads their surface uses, instead of importing a monolithic CSS bundle or
hand-concatenating direct style functions. Non-HTML lanes prove they do not
request the HTML/CSS capability closure through
`test/01_unit/app/ui/render_capability_spec.spl` and
`test/03_system/app/ui/feature/low_dependency_ui_dynsmf_dependency_gate_spec.spl`.

### Simple GUI API

The GUI API expresses UI intent. It should not call Electron, Tauri, Chrome,
CUDA, Metal, Vulkan, or OpenCL APIs directly. GUI logic remains pure Simple
unless an optimization plugin is invoked through a typed backend contract.

### Simple Web API

`src/app/ui.web` is the host-safe transport and web adapter boundary. It owns
snapshots, patches, commands, taskbar/window messages, and session envelopes.
It may accept HTML text for compatibility, but the preferred future path is a
typed GUI AST to WebRender IR transfer that avoids string parsing on hot redraw
paths.

### Render IR and Draw IR

`WebRender IR` records renderable UI facts: style items, surfaces, text runs,
images, dirty regions, screen config, and event callback ids. `Draw IR` lowers
that into execution batches: primitive operations, composition grouping,
callback locality, source/style provenance, and CPU/GPU placement hints.

Draw IR consumers must not infer layout or style from raw HTML/CSS. Conversion
layers resolve GUI AST style intent or HTML AST/CSS information before emitting
Draw IR commands. The batch keeps the source identity (`manual`, `gui_ast`,
`html_ast`, or `wm_scene`), HTML tag/node identity when present, CSS selector or
class when present, and a style revision. That metadata is for diagnostics,
cache invalidation, replay, and GPU batch grouping; primitive commands remain
the execution truth.

The canonical Draw IR schema is `simple-draw-ir-v2`. The typed model includes
box geometry/style metadata plus edge/path/image/group/port command kinds; SDN
inspection uses `src/lib/common/ui/draw_ir_sdn.spl` as an interchange skin over
the same `DrawIrComposition`, not a second model.

UI test helpers consume Draw IR through the shared test contract, not through
renderer-private files or backend handles. Protocol v1 `/api/test/*` endpoints
remain stable; Protocol v2 Draw IR endpoints are optional and capability-gated:
`/api/test/draw-ir`, `/api/test/draw-ir?id=...`,
`/api/test/draw-ir/diff`, and `/api/test/draw-ir/layout?id=...`. SPipe remains
the test harness: new UI/Draw IR specs import `use std.spec`, and `std.spipe`
remains an alias for existing specs.

This boundary is the best next refactoring target because it reduces coupling
between `src/app/ui.web`, `src/lib/common/ui/web_render_api.spl`, and
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_engine2d_renderer.spl`.

The current bootstrap contract lives in `src/lib/common/ui/draw_ir.spl`. It
defines `DrawIrEmbeddingConfig`, `DrawIrCommand`, `DrawIrBatch`,
`DrawIrSourceInfo`, `DrawIrComposition`, `DrawIrEventTargetContext`,
`Simple2dDrawIrPlan`, and `Simple2dDrawIrCompositionPlan` so the Simple 2D
advanced boundary can accept explicit size, location, layer, transparency,
surface/component identity, source/style provenance, event target context,
backend target, and fallback metadata before GPU execution exists.

Window-manager composition is projected by
`src/lib/common/ui/window_scene_draw_ir.spl`. It converts `SharedWmScene`
chrome, taskbar, and visible windows into ordered Draw IR batches keyed by
`shared_wm_scene_layout_key(scene)`. The first Engine2D-facing acceptor lives in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`; it executes supported
`rect`, `text`, and caller-resolved `image` Draw IR commands through the
existing Engine2D facade, presents the completed composition, and returns
readback pixels plus CPU/GPU fallback metadata. Resolved IMAGE commands may use
destination dimensions distinct from their source and lower through the same
checked Vulkan blit with CPU-matching nearest-neighbor sampling; non-opaque
scaled work uses the existing checked src-over mode after opaque initialization.
SimpleOS x86_64, AArch64, and
RV64 canonical boot-desktop source frames enter through
`src/os/compositor/engine2d_wm_frame_executor.spl`; invalid
or duplicate top-level `WmContentFrame` resources fail closed, and nested IMAGE
projection remains explicit unfinished work rather than omitted pixels. Real
host-GPU Draw IR execution remains a backend job. Host runtime-queue integration
lives separately in `draw_ir_runtime_adv.spl`; importing the core executor does
not pull host-queue runtime APIs into the baremetal closure. RV64 dynamic
VirtIO mode discovery and transfer/flush presentation stay in its architecture
display facade; they are transport around the canonical composition, never a
parallel GUI/Web/2D renderer.

### Render Optimization Plugin

The plugin is an acceleration boundary, not a GUI ownership boundary. It may be
implemented by optimized Simple backends, host GPU libraries, or compiled
kernel artifacts, but the input and output remain Simple-owned contracts.

Required interface shape:

```
RenderOptimizationPlugin
  supports(capabilities, draw_ir) -> SupportReport
  estimate_cost(draw_ir, dirty_regions) -> CostReport
  prepare(draw_ir, cache_key) -> PreparedBatch
  execute(prepared_batch, target_surface) -> ExecuteReport
  readback(surface, region) -> PixelEvidence
```

Fallback to the CPU/SIMD backend is mandatory. The CPU path is the correctness
oracle for tests, screenshots, capture hashes, and unsupported GPU devices.

Backend selection is split into two explicit lanes. The drawing lane owns
framebuffer-visible primitive rendering, present, and readback. The processing
lane owns generated kernels, filter/layout compute, vector/font offload, and
SIMD/GPU preparation work. A backend may implement both lanes on one device, but
that is a `combined` lane plan rather than an implicit assumption. The current
contract is in `src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl`.
Font offload evidence is intentionally split by font class:
`src/lib/gc_async_mut/gpu/engine2d/vector_font_offload.spl` proves when vector
glyph pixels have actually returned from a GPU path, while
`src/lib/gc_async_mut/gpu/engine2d/bitmap_font_offload.spl` records the current
bitmap-font state as CPU glyph preprocessing plus optional GPU copy/upload and
the `bitmap_glyph_raster` generated-kernel launch plan. The portable compiler
emitter and the CUDA/OpenCL/HIP Engine2D paths expose
`simple_2d_bitmap_glyph_raster_u32`; CUDA routes the generated operation through
`bitmap_glyph_raster_kernel(...)` and classifies checksum readback through
`CudaSession.readback_evidence(...)`, OpenCL binds the packed
glyph/destination/size/color arguments, and HIP preflights the same packed
shape before launch. `bitmap_glyph_raster_expected_pixels(...)` maps the glyph
mask to the expected color/zero output, and
`bitmap_glyph_raster_checksum(...)` derives the expected checksum used by
`bitmap_glyph_raster_readback_evidence(...)`.
`bitmap_glyph_raster_mask_readback_evidence(...)` is the preferred device
sample wrapper because it uses `bitmap_glyph_raster_mask_checksum(...)` to
derive the expected checksum directly from the glyph mask and color, avoiding a
temporary expected-pixel allocation and avoiding caller-supplied expected
values. That readback wrapper is the production proof gate and only marks
bitmap glyph rasterization ready after generated-kernel submit and
checksum-matched device readback. Do not treat generated copy/upload, source
export, launch binding, preflight, or raster-plan evidence as GPU-side bitmap
glyph rasterization until that readback proof passes.

### Event Target Translation

Window-level event targeting is resolved through
`src/lib/common/ui/window_scene.spl`. Pointer translation returns a component
kind, local event coordinates, target id, callback/window identity, backend
target metadata, and cache status. The cache key includes the scene layout key
and pointer/backend input key; window movement, resize, layer, or composition
changes must produce a new scene key so stale target translations are rejected.
That same scene key is embedded in WM Draw IR composition so event targeting and
draw processing invalidate together. The event-to-draw-processing handoff is
represented by `DrawIrEventTargetContext`: it maps the translated event target
and local coordinates onto a Draw IR batch, surface/component id, source kind,
and backend target, while rejecting stale scene keys before the renderer or
future GPU plugin receives the event context.

### Engine2D and Primitive Draw

Engine2D remains the shared drawing and processing execution layer. It should
expose stable primitive operations and backend sessions while hiding
backend-specific device details from UI and wrapper code. Drawing backends
handle primitive draw, framebuffer ownership, present, and readback. Processing
backends handle compute kernels, generated artifacts, filters, and offload.
Draw processing may use CPU scalar, CPU SIMD, OpenCL, CUDA, HIP, Vulkan, Metal,
or WebGPU, but GUI code sees only the typed Simple 2D and plugin contracts.
Host/GPU event ownership is explicit: `host_gpu_event_queue.spl` records the
event decision, submit, and receipt evidence, and
`host_gpu_draw_ir_event_flow.spl` records derived Pure Simple forward/backward
phase evidence around that decision. Unresolved targets, stale target-cache
events, and host-semantic mutation stay on the host; coarse Draw IR
render/effect batches can forward from host to the GPU lane and report a
completed GPU-to-host backward receipt.

Production status is deliberately split by proof type:

| Layer | Current evidence | Production meaning |
|---|---|---|
| Evidence adapter | `src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` and `host_gpu_draw_ir_event_flow.spl` produce deterministic decision, submit, receipt, forward, backward, Pure Simple queue-state, and Draw IR routing summaries. GC Engine2D paths keep export-only compatibility shims. | Proves host-vs-GPU routing policy, packet-size/fallback classification, explicit forward/backward phase evidence, and an in-language emit -> submit -> complete -> drain lifecycle model. It is not by itself proof that a GUI/web frame was drained through a backend. |
| Runtime queue emission | `target.later(...) gpu` interpreter handling and `engine2d_host_gpu_event_submit_to_runtime` can emit queue packets and expose queue counters, submit/complete lifecycle state, and drain status through runtime externs. `Engine2dHostGpuPureQueueState` mirrors the same lifecycle in Pure Simple without depending on runtime extern counters. `Engine2dDrawIrPayloadSummary` carries a deterministic descriptor with schema, batch/source/surface identity, command count, packet bytes, command checksum, serialized SDN byte count, and one-batch `draw_ir_to_sdn` text; `Engine2dHostGpuRuntimeSubmitResult.payload_summary` carries that serialized SDN payload for Draw IR submits. Low-level runtime queue packets preserve payload byte size, hash, and bounded UTF-8 text through completion/drain receipts. | Proves packets can enter the host/GPU runtime queue, that HostGpuLaneBegin/End now drive forward submit and backward completion receipts, and that the Draw IR bridge carries serialized payload evidence beyond numeric counters. Broader backend/session command-buffer receipts are still required for production parity. |
| Web artifact diagnostics | `src/lib/common/ui/web_render_api.spl` stores `WebRenderArtifact.queue_*`, backend handle, and readback backend/source/pixel-count/checksum/reason metadata; `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl` attaches runtime queue evidence for GPU-selected artifacts; `src/app/ui.browser/backend.spl` mirrors it as `last_artifact_queue_*` and `last_artifact_gpu_readback_*`. | Proves queue evidence and backend readback provenance can be carried through the web-render artifact contract and a focused `BrowserBackend.render_frame` GPU frame. |
| Backend readback | Generated/native reports under `doc/09_report/` prove backend-specific readback when the backend is available: Vulkan Engine2D readback is `pass`, CUDA generated 2D readback is `pass` with `submit_attempted=true` and `readback_available=true`, OpenCL generated 2D readback is `pass` with the same booleans, and Linux Metal/ROCm generated readback is typed `unavailable` with submit/readback false. | Proves backend submit/sync/readback for the reported backend fixtures and is consumed by the production GUI/web queue-readback wrapper. The wrapper's Readback Matrix must expose submit/readback columns so Spark and normal-LLM reviews can reject verdict-only or upload-only evidence. |
| GUI/web integration | `src/app/ui.browser/backend.spl` owns a local UI event queue, host event roundtrip telemetry, scheduling-only host/GPU event-flow summary fields for dispatched input events, an Engine2D pixel artifact path, and queue diagnostic fields. Generated widget HTML uses the deterministic widget raster path, then presents through Engine2D for bounded backend readback. Focused `BrowserBackend.render_frame` specs expose queue diagnostics, frame payload size/hash/text receipts, a widget-semantic Draw IR dispatch receipt with dispatch payload size/hash/text, GUI AST source evidence, widget-id rect commands, text command-count evidence, image command/URI evidence, queued-command event-target context resolution, conservative in-process render timing, a positive Vulkan backend handle propagated from `Engine2DReadback.backend_handle`, Engine2D readback source/pixel-count/checksum/reason metadata, and cache-hit reset; host event roundtrip specs separately prove BrowserBackend ingress/dispatch/render telemetry. Synthetic handle `7` is limited to isolated runtime queue roundtrip tests. CUDA, OpenCL, Metal, OpenGL, ROCm, and Vulkan device-readback branches preserve concrete device-readback handles when their initialized device path is used; WebGPU preserves positive `surface_upload` provenance handles when an initialized surface accepts upload; DirectX preserves positive `swapchain_present` provenance handles when an initialized swapchain accepts presentation; CPU/cache/not-requested fallbacks remain handle `0`. BrowserBackend input-event host/GPU fields are scheduling evidence until tied to a live runtime packet/readback receipt for that input event. Image URI Draw IR command evidence is not the same as decoded-image rendering; the Engine2D advanced Draw IR path can render caller-provided resolved ARGB pixel buffers keyed by `image_uri`, while unresolved, invalid, PNG, JPEG, and WebP image sources still fail closed as skipped image commands until the asset resolver and decode pipeline feed valid pixels. | `scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs` is the canonical production gate for GUI/web event roundtrip -> runtime packet -> payload text receipt -> widget-semantic Draw IR dispatch payload receipt -> queued-command event context -> positive backend-handle receipt -> same-frame backend device readback on this lane. Its Platform Spark/Normal-LLM table must expose the compact `linux_gui_web` row (`event=browser-input-1; packet=1; source=device_readback; checksum=...`) and DirectX native verdict/gate/child-gate fields. DirectX/WebGPU presentation/upload provenance is guarded so it cannot count as `device_readback`. |

The current production posture is evidence-gated and fail-closed. Adapter
summaries, runtime queue emit/drain receipts, BrowserBackend frame receipts,
and Vulkan/CUDA/OpenCL readback reports remain separate layers. The canonical wrapper
must be the source of truth for whether the joined GUI/web run currently proves
event queue -> runtime packet -> positive backend-handle receipt -> backend device readback receipt.
Linux Metal and ROCm/HIP remain typed host-unavailable unless those runtimes are
present.
The wrapper report must keep high-signal proof fields table-visible: the
Readback Matrix includes submit/readback availability for generated 2D child
backends, and the Platform Spark/Normal-LLM table includes a `linux_gui_web`
event/readback row plus a DirectX native verdict/gate row.

Known runtime/production gaps:

- Compiler/interpreter GPU lane queue packets now consume
  `host_gpu_active_backend_handle()`, submit at lane begin, and complete after
  lane end; they still complete as typed `UNAVAILABLE` when no backend registers
  a positive active handle.
- Rust and C runtime queues now share a `1024` pending-packet capacity, with
  Rust runtime coverage for overflow rejection and post-drain reuse. A typed
  overflow/backpressure status remains a follow-up if callers need to
  distinguish capacity rejection from invalid arguments.
- A two-phase runtime submit/complete path now exposes observable in-flight
  `SUBMITTED` before terminal `COMPLETED` or `UNAVAILABLE` status.
- Interpreter lane `END` accounting is exception-safe for lane body errors in
  the Rust builtin interpreter and the Pure Simple backend interpreter. The
  statement-lowered Rust HIR path now injects lane-local cleanup before body
  `return` statements and still needs compiler-level cleanup/finally support
  before claiming arbitrary body-error cleanup.
- Runtime packets can now expose a submitted backend-handle value through
  `host_gpu_queue_last_backend_handle()`. BrowserBackend Vulkan frames
  mirror the positive `Engine2DReadback.backend_handle` plus readback
  pixel-count/checksum/reason metadata from the same-frame device readback, and
  CUDA/OpenCL/Metal/OpenGL/ROCM/Vulkan device-readback
  implementations preserve their concrete handle when initialized. WebGPU
  preserves `surface_upload` handles for upload provenance, and DirectX
  preserves `swapchain_present` handles for presentation provenance; neither is
  backend device-readback proof. Cache, CPU mirror, and not-requested paths
  reset the handle to `0`.
- `BrowserBackend.render_frame` now completes for generated widget frames and
  has focused queue/readback coverage, including real Vulkan readback
  provenance and cache-hit reset.

Documentation and test reports must distinguish the current Linux production
gate from stronger all-platform backend-native handle proof. The joined GUI/web
frame proof is currently Vulkan-backed: a single Linux run proves GUI/web event
queue -> runtime packet -> positive backend-handle receipt -> backend device
readback for that path. CUDA and OpenCL are child backend readback fixtures in
the same production wrapper, Metal and ROCm/HIP may be host-unavailable, and
DirectX/WebGPU remain presentation/upload provenance until they have positive
same-frame device-readback evidence.

SimpleOS RV64 desktop uses the same evidence shape for the QEMU GPU lane. The
multi-config contract in `src/os/simpleos_config_matrix.spl` exposes
`simpleos_engine2d_vulkan_required_evidence_keys()`: runtime backend must be
`vulkan`, scene must be `vulkan-engine2d`, Simple2D command evidence must pass,
a Vulkan device name and viewport must be recorded, readback must have a
checksum and nonblank status, and QEMU GPU readback must pass. CPU/software
fallback is useful diagnostic evidence, but it is not a Simple2D-over-Engine2D
Vulkan pass for SimpleOS.

The same module exposes `qemu_riscv64_engine2d_vulkan_bridge_plan()` as the
implementation-facing bridge for this path. It binds QEMU SimpleOS to the
`qemu-riscv64-desktop` profile, `virtio_gpu` framebuffer drawing,
`vulkan` Engine2D processing, `virtio-gpu-device`, the `vulkan-engine2d`
scene, `draw_ir-to-engine2d` Simple2D commands, Engine2D device readback, QMP
screendump readback, RenderDoc `capture-simple`, and the
`simpleos-desktop-four-windows` WM comparison scene. A CPU processing fallback,
missing QMP screendump requirement, or non-Simple RenderDoc mode leaves the
bridge blocked.

On Windows, `scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`
normalizes the available artifacts into that contract. It reads
`build/gui-web-2d-vulkan-env/evidence.env` when present, checks QEMU
`qemu-screendump.ppm` for nonblank readback, validates SimpleOS RenderDoc
`.rdc` magic and capture logs, and emits the `simpleos_engine2d_*` plus
`simpleos_renderdoc_*` rows consumed by
`scripts/check/check_simpleos_multiconfig_live_evidence.spl`. The aggregate
checker also reports `simpleos_engine2d_vulkan_bridge_status`; this is a bridge
alignment diagnostic, while `simpleos_engine2d_vulkan_evidence_status` remains
the live Vulkan/readback completion gate.

The same Windows normalizer supports `-ProbeHostVulkan` for host readiness
diagnostics. That mode records `vulkaninfo --summary`, visible SDK tools
(`glslangValidator`, `spirv-as`, `dxc`), Chrome/Electron presence, RenderDoc
tool presence, and the focused browser-backing rows. These rows do not satisfy
the SimpleOS gate by themselves: a source evidence file can be present while
the runtime backend, viewport, checksum, QEMU readback, browser backing, and
RenderDoc capture remain blocked.

Backend preference has two layers. `backend_full_preference_order()` records the
stable user-visible order, with explicit native surfaces first:
`baremetal`, `virtio_gpu`, Metal, CUDA, ROCm/HIP, Qualcomm, Vulkan, DirectX,
OpenCL, OpenGL, Intel, WebGPU, CPU SIMD, software, and CPU. DirectX is a
drawing backend with D3D11 semantics: native d3d11 on Windows, DXVK/vkd3d over
Vulkan on Linux, with `leaf=dlopen|structured` evidence from the ICD shim
chain (`src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl`). The automatic
width/height-only probe remains `backend_default_priority_order()` and starts at
Metal because `baremetal` and `virtio_gpu` require a caller-owned platform or
VirtIO framebuffer. Diagnostics and reports should use
`backend_preference_summary()` from
`src/lib/nogc_async_mut/gpu/engine2d/helpers_availability.spl` so guides,
tests, and startup evidence describe the same order.

Text fallback helpers must keep glyph-pixel loops separate from layout advance
padding. The buffer is prefilled with background pixels, so anti-aliased glyph
rendering should touch only the glyph coverage width and leave advance gaps or
font-size padding rows as background. Specs assert the pixel-count contract,
bottom padding rows, and advance-gap background to keep this startup hot path
safe for loop-hoisting and bounds-check work.

### Startup dynSMF Libraries

The low-dependency lane treats standard library-like capabilities as
precompiled dynSMF entries: `file_io`, `net_io`, `render2d`, `web_renderer`,
`gui_renderer`, `tui_renderer`, and `ui_html`. Startup constructs a session through
`src/app/startup/dynsmf_autoload.spl`, applies `--no-dynsmf`,
`--disable-dynsmf=<ids>`, `SIMPLE_DYNSMF=0`, and
`SIMPLE_DYNSMF_DISABLE=<ids>`, validates generated `build/dynsmf/*.smf`
artifacts, and then loads enabled entries through `smf_dlopen`.

The session owns handles and generation metadata so interpreter-mode tests can
unload a library, observe stale symbol evidence, and reload without retaining
process-global state.

## Hot-Path Policy

Hot redraw paths must avoid:

- repeated full-tree scans;
- repeated file reads;
- subprocess retries;
- HTML/CSS string parsing when a typed GUI AST or already-resolved HTML AST is
  available;
- re-resolving CSS for Draw IR batches whose `style_revision` has not changed;
- device probing per frame;
- hidden wrapper-specific renderer forks.

Capability probes run at startup or explicit re-probe time. Plugin cache keys
must include backend id, device capability version, shader/kernel artifact
version, Draw IR schema version, source kind/id, style revision,
style/font/resolved-image cache versions, and fallback reason metadata.

## Migration Order

1. Extract typed `WebRender IR` and `Draw IR` contracts under `src/lib/common/ui`.
2. Split the large web-to-Engine2D renderer into parser/scan helpers, IR
   extraction, and draw execution modules.
3. Route GUI AST redraw through the typed IR path before the HTML parser path.
4. Add the render optimization plugin interface with CPU fallback first.
5. Split concrete backend implementations into drawing-lane and
   processing-lane capabilities before adding direct GPU Draw IR execution.
6. Add GPU backend implementations behind capability probes and evidence
   reports.
7. Keep Tauri, Electron, Chrome, and browser wrappers thin; they should not own
   renderer policy.

### WM Runtime Dispatch

`src/lib/common/ui/wm_runtime_dispatch.spl` converts backend-neutral
`SharedWmDispatchResult` values into stable `WmRuntimeDispatchCommand` structs
with kind, target_id, app_id, window_id, payload, and handled flag. This
adapter lets host WM runtimes (web bridge, SimpleOS WM, native host) consume
WM commands without depending on the internal window-scene dispatch model.
`WmRuntimeShellState` tracks launched apps, focused window, drag surface, and
last command for shell-side bookkeeping.

The web host bridge in `src/app/ui.web/wm_runtime_bridge.spl` consumes these
dispatch commands and forwards them to the web adapter protocol.

## Source File Map

| Layer | File | Purpose |
|---|---|---|
| Draw IR contract | `src/lib/common/ui/draw_ir.spl` | `DrawIrCommand`, `DrawIrBatch`, `DrawIrComposition`, `DrawIrSourceInfo`, `DrawIrEmbeddingConfig`, `DrawIrEventTargetContext`, `Simple2dDrawIrPlan` |
| Draw IR SDN skin | `src/lib/common/ui/draw_ir_sdn.spl` | Deterministic tab-indented SDN import/export over `DrawIrComposition` |
| Draw IR Draw.io skin | `src/lib/common/ui/draw_ir_drawio.spl` | Draw.io mxGraph import/export over the same `DrawIrComposition` model |
| WM scene | `src/lib/common/ui/window_scene.spl` | `SharedWmScene`, `SharedWmWindow`, event target translation, scene layout keys, cache-safe pointer targeting |
| WM → Draw IR | `src/lib/common/ui/window_scene_draw_ir.spl` | WM scene composition into ordered Draw IR batches (desktop, chrome, windows by z-order, top-level content IMAGE projection) |
| WM dispatch | `src/lib/common/ui/wm_runtime_dispatch.spl` | `WmRuntimeDispatchCommand`, `WmRuntimeShellState`, backend-neutral WM command adapter |
| Engine2D Draw IR | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl` | `Engine2dDrawIrAdvResult`, Draw IR executor (rect/text/resolved image, present, CPU fallback, pixel readback) |
| Engine2D Draw IR runtime queue | `src/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_adv.spl` | Optional host runtime-queue adapter, kept out of the core/baremetal import closure |
| SimpleOS WM frame executor | `src/os/compositor/engine2d_wm_frame_executor.spl` | Persistent production DrawIR/Engine2D owner with exact content-frame validation and fail-closed resource coverage |
| Backend lane | `src/lib/nogc_async_mut/gpu/engine2d/backend_lane.spl` | Drawing vs processing lane split contract |
| Host/GPU event queue | `src/lib/nogc_async_mut/gpu/engine2d/host_gpu_event_queue.spl` | Host event decision, queue submit, queue receipt evidence, and Pure Simple queue lifecycle state |
| Host/GPU Draw IR flow | `src/lib/nogc_async_mut/gpu/engine2d/host_gpu_draw_ir_event_flow.spl` | Draw IR event routing into host or GPU queue lanes with explicit forward/backward phase evidence |
| DirectX drawing backend | `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl` | D3D11 drawing backend; native on Windows, DXVK/vkd3d→Vulkan on Linux, platform probe + leaf evidence |
| DXVK/vkd3d ICD shims | `src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl` (+ `dxvk_d3d9/10/11.spl`, `vkd3d_d3d12.spl`) | D3D→Vulkan dispatch chain with `leaf=dlopen\|structured` evidence; Linux setup via `scripts/setup/setup-directx-linux.shs` |
| Renderer capability | `src/app/ui.render/capability.spl` | Implementation-free HTML/CSS/TUI renderer capability metadata |
| TUI widget shim | `src/app/ui.render/widgets.spl` | TUI-only compatibility wrapper that avoids HTML/CSS implementation imports |
| HTML widgets | `src/app/ui.render/html_widgets.spl` | HTML-capable widget renderer implementation |
| Component CSS | `src/app/ui.render/css.spl` | Component-scoped CSS payload selector through `css_for_components` |
| UI dependency gate | `src/app/ui/dependency_closure_gate.spl` | Exact-prefix dependency closure verifier for TUI and adapter boundaries |
| dynSMF session | `src/os/smf/dynsmf_session.spl` | Precompiled dynSMF manifest, checked load/autoload, unload/reload evidence |
| dynSMF startup | `src/app/startup/dynsmf_autoload.spl` | CLI/env policy adapter for checked default dynSMF autoload |
| Web render API | `src/lib/common/ui/web_render_api.spl` | WebRender IR transport |
| Web bridge | `src/app/ui.web/wm_bridge.spl` | Web host WM adapter |
| Web WM bridge | `src/app/ui.web/wm_runtime_bridge.spl` | Web host WM runtime dispatch consumer |
| Shared MDI demo | `src/app/ui_shared_mdi/main.spl` | Backend-neutral MDI IPC demo; environment toggles go through `app.io.env_ops.env_get` instead of local runtime env declarations |

## Host Shell Targets

| Shell | App path | Default? | Notes |
|---|---|---|---|
| Web | `src/app/ui.web` | **Default** | Primary host; web adapter protocol |
| TUI | `src/app/ui.tui` | n/a (separate lane) | Terminal surfaces |
| TUI+Web | `src/app/ui.tui_web` | n/a | TUI over web transport |
| Standalone | `src/app/ui.standalone` | non-default | Native window, no wrapper |
| Tauri | `src/app/ui.tauri` | non-default | Tauri webview shell |
| Electron | `src/app/ui.electron` | non-default | Electron shell; renders internal windows (MDI-in-one-window) inside its single `BrowserWindow`, verified 2026-07-05 — see below |
| Chromium | `src/app/ui.chromium` | non-default | In-tree engine wearing Chromium naming (ADR-002), not a real-Chrome delegate |
| Browser | `src/app/ui.browser` | non-default | Browser-only target |
| VS Code | `src/app/ui.vscode` | non-default | VS Code webview extension |
| CLI | `src/app/ui.cli` | non-default | CLI-mode UI |
| IPC | `src/app/ui.ipc` | non-default | IPC bridge |
| MCP | `src/app/ui.mcp` | non-default | MCP UI integration |
| Render | `src/app/ui.render` | non-default | Headless render target |
| Test API | `src/app/ui.test_api` | non-default | Test harness |

All shells are thin — they forward input and present frames. GUI policy,
state, layout, event routing, and Draw IR remain Simple-owned.

## Backend hierarchy (2026-07-05)

The maintainer's target containment tree for `ui/gui` (see
`00_ui_architecture.md` § Target Layer Hierarchy) is:

```
gui
├── electron wrapper + electron   # non-default; supports internal windows (verified 2026-07-05)
├── core                          # simple gui core: internal window rendering — WM uses this
└── web server ui                 # DEFAULT
    └── web
        ├── chrome wrapper + chrome   # delegates to Chrome (comparison/capture only today)
        └── core                      # CORE simple web renderer (HTML/CSS -> layout -> paint)
            └── simple 2d renderer (engine2d)
                ├── cpu simd (x86, riscv, arm/aarch64)
                ├── directx
                ├── vulkan
                └── metal
```

This is a containment/default-selection view, distinct from the data-flow
"Target Stack" pipeline earlier in this document — both describe the same
system from different axes and must agree on components.

Current gaps versus this target (see `00_ui_architecture.md` for full
status table and evidence paths):

- **Electron internal windows — resolved 2026-07-05.** `bridge.js` still
  spawns exactly one top-level `BrowserWindow`, but it now renders internal
  windows *inside* it as positioned `.wm-window`/`.wm-titlebar` DOM elements
  (`electronWmInitScript`/`receiveElectronMessage` in `bridge.js`), the same
  class contract `window_scene_draw_ir.spl` (`WM_DRAW_IR_DESKTOP_SURFACE =
  "wm-desktop"`) and the web lane use for `gui/core`. Verified with a real
  4-window screenshot + JSON proof (drag, click/input/key routing,
  minimize/maximize/close, taskbar) via
  `scripts/check/check-electron-mdi-evidence.shs` +
  `scripts/check/validate-electron-mdi-proof.js`. `main.spl`'s `notify()` was
  already wired to Electron's real `Notification` API; `open_file_dialog()`
  previously printed a `fileDialog` request `bridge.js` had no handler for —
  `bridge.js` now calls the real `dialog.showOpenDialog`/`showSaveDialog` and
  round-trips the result back to `open_file_dialog()` over stdin as a
  `fileDialogResult` message. Remaining gap: the gate script only runs under
  Linux+Xvfb (`xvfb-run`) and its `SIMPLE_BIN` auto-detect glob prefers a
  Linux binary path even on macOS, so it must be invoked with `SIMPLE_BIN`
  set explicitly there; this backend is still dev-preview-only and not in CI.
- **Chrome delegation.** No production path switches the web renderer to a
  live Chrome process; `tools/chrome-live-bitmap/capture_html_argb.js` and
  the `*-render-log-compare.shs` gates are comparison/capture tooling, which
  does satisfy the "Metal render-log capture for comparison" requirement,
  but is not a runtime rendering backend.
- **`simple_web_engine2d_renderer.spl` fixture-faking.** Still contains
  fixture/heuristic discriminator branches (e.g. `"deterministic
  compatibility fixture"`) that route known corpus/contract fixtures through
  calibrated shortcuts instead of the generic layout path; being removed.

## Verification Requirements

Every implementation of this architecture needs evidence for:

- semantic equivalence across TUI, GUI, web, and wrapper paths where the command
  model overlaps;
- TUI and renderer dependency closure gates proving HTML/CSS/GUI/web
  implementations stay outside non-capable lanes;
- component-scoped CSS selector evidence proving adapters request only the
  style payloads they use;
- checked dynSMF artifact, startup policy, unload, stale symbol, and reload
  evidence for stdlib-like renderer/runtime capabilities;
- CPU fallback rendering for every Draw IR feature;
- plugin fallback reason reporting;
- pixel/capture/hash evidence for GPU execution claims;
- host/GPU queue evidence that names the proof layer: adapter decision/submit,
  runtime queue emission/drain, backend readback, or full GUI/web queue-drain
  integration;
- warm redraw latency, input-to-paint latency, max RSS, cache-hit behavior, and
  startup probe cost;
- focused backend startup-order evidence:
  `test/05_perf/graphics_2d/backend_preference_startup_spec.spl` verifies the
  Engine2D auto/full preference order and bounds the pure helper startup path
  without requiring local GPU hardware;
- WM dispatch command parity: `wm_runtime_dispatch_command` output must match
  across web bridge, SimpleOS WM, and standalone hosts;
- `doc/06_spec` layout safety: executable specs stay under `test/**`, not
  under generated/manual spec docs.

## UI Test Architecture

The canonical test-access architecture for TUI, GUI, web, and 2D lives in
`doc/04_architecture/ui/ui_test_architecture.md` and its TLDR companion
`doc/04_architecture/ui/ui_test_architecture_tldr.md`. Two layers are unified
behind one configurable interface (`tui` | `gui` | `both`):

- **HTTP protocol path** - `UITestClient` over `/api/test/*` for S4 surfaces
  (web, tui-web); returns `ElementInfo`.
- **SGTTI in-process path** - `common.ui.win_text_access` +
  `os.compositor.gtti` give GUI/web/2D a headless semantic tree through the
  compositor source in `WM_MODE_HIDDEN`, over canonical `UiAccessNode` values.
  TUI joins through the `UIState -> win_text_simple_ui_snapshot` lift.

New UI specs import `use std.spec`; `std.spipe` remains a compatibility alias.
Helpers such as SGTTI checks and future `expect_draw` run inside SPipe
scenarios and do not replace `expect` or the canonical matcher set.

Semantic SGTTI evidence and pixel evidence run together. SGTTI proves
identity/state/text/structure; existing bitmap gates and Engine2D readback stay
the pixel oracle. Draw IR batches/compositions can be lifted with
`sgtti_snapshot_from_draw_ir_batch` and
`sgtti_snapshot_from_draw_ir_composition`, letting Engine2D specs assert the
pre-raster node tree before pixel readback. Draw IR Protocol v2 inspection
depends on SGTTI. Improvement plan:
`doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md`.

## GUI Sanity Apps (pure-Simple lane, macOS)

Three small on-screen apps exercise the pure-Simple drawing lane (on macOS that
is the Engine2D **CPU/aarch64-NEON** and **Metal** backends). They are the quick
"does the GUI still render" sanity set after any GUI/engine2d/web change:

| Lane | App | What it proves |
|------|-----|----------------|
| 2D rendering | `examples/06_io/ui/engine2d_cpu_simd_gui.spl` (CPU) / `engine2d_metal_gui.spl` (Metal) | Engine2D primitives: text, rect, circle, line, gradient, rounded-rect |
| GUI widgets | `examples/06_io/ui/widget_showcase_gui.spl` | Widget chrome drawn on the CPU lane: button, checkbox, text field, progress bar, list, with legible labels |
| HTML rendering | `examples/06_io/ui/web_text_gui.spl` (text page) / `web_render_file_gui.spl <file.html>` | Web layout → Engine2D CPU: real laid-out, legible glyph text |

Those three apps render **static, non-interactive** scenes — they sanity-check
the drawing surfaces, not the interactive GUI (the HTML one uses the real web
renderer; the 2D/widget ones draw primitives directly, which is fine for a demo
but not a template for an app). The **interactive WM/MDI app** is the real
pipeline and must not be re-implemented by hand-drawing engine2d primitives:

| Lane | App | What it proves |
|------|-----|----------------|
| Interactive WM/MDI | `src/os/hosted/hosted_entry.spl` | `HostCompositor` + `seed_host_compositor_shared_mdi` rendering Simple Web MDI app content through `HostedWinitBufferBackend`, with real event routing (`comp.pointer_move`, `comp.handle_left_button` — click-focus, titlebar drag, close-X; keyboard Tab/W/M/R/Esc). Widget→pixels uses the real `common.ui.builder` → `init_state` → `app.ui.render.html_widgets.render_html_tree` → `simple_web_render_html_to_pixels_with_engine2d_backend` path; hit-testing via `shared_wm_translate_pointer_event` (`src/lib/common/ui/window_scene.spl`). |

Verify the interactive WM with the framebuffer/logic gate (not a screenshot):
`scripts/check/check-shared-wm-renderer-unification-evidence.shs` expects
`shared_wm_renderer_unification_status=pass` and `logic_passed >= 4`. macOS
caveat: the hosted winit window can present blank — the documented winit bug
`doc/08_tracking/bug/macos_winit_window_not_displayed_2026-05-28.md` — so trust
the gate, not the live window. Pure-Simple web render is real but
interpreter-bound (~minutes/frame); the fast live path is Draw IR
(`engine2d_draw_ir_adv_batch` in
`src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl`), whose widget-tree→Draw IR
converter is the not-yet-built "preferred next refactor".

Launch on macOS (registers the process with the window server via a throwaway
`.app` bundle, then nudges the window on-screen):

```sh
scripts/gui/macos-gui-run.shs examples/06_io/ui/engine2d_cpu_simd_gui.spl
scripts/gui/macos-gui-run.shs examples/06_io/ui/widget_showcase_gui.spl
scripts/gui/macos-gui-run.shs examples/06_io/ui/web_text_gui.spl
```

Verification approach (avoid screen-capture flakiness): the **framebuffer is the
ground truth**. Run an app headless and dump `read_pixels()` to a P3 PPM via
the stdlib/app file facade or the lane's evidence wrapper, then inspect/convert
it — this proves the lane renders independent of window-server/compositor
state. The live `.app` launch is the secondary, human-in-the-loop check. (See
`scripts/check/check-macos-gui-live-window-evidence.shs` for the capture gate.)

Caveats:
- The **2D lane is fast**; the **web-layout lane is interpreter-bound (~1.5 ms/px)**,
  so keep web/widget-via-web surfaces small (≤ ~160×120) for one-shot renders.
- The launcher and capture gate compute repo-root from their own location; scripts
  living under `scripts/gui/` and `scripts/check/` must use `dirname/../..` (two
  levels), not `dirname/..` — getting this wrong silently resolves repo-root to
  `scripts/` and breaks every GUI launch.

## Realized 2026-06-15 — one API, common/web/text renderers

This iteration moved the stack toward the target above (see design doc
`doc/05_design/ui/renderer_unification_2026-06-15.md`):

- **One 2D API, env-selected lane.** `Engine2D.detect_best_backend()` now honors
  `SIMPLE_2D_BACKEND` (e.g. `cpu_simd`, `software`, `cuda`, `vulkan`) when the
  named lane initializes, else auto-probes. The `RenderBackend` trait was already
  shared by every SIMD-CPU/GPU lane; selection is now config/environment-driven
  without per-call-site changes. Engine2D env selection and the opt-in Vulkan
  GLSL gate read configuration through the stdlib I/O facade instead of local
  runtime env declarations.
- **Three renderers, shared cheap base.** common renderer
  (`lib/common/render_scene` cascade + `lib/common/ui/draw_ir`) → web renderer
  (`browser_engine`) and slim text renderer (`editor/render/md_renderer.spl`).
  The TUI keeps zero GPU imports by default but derives style from the shared
  `office_style_resolver` cascade; the opt-in `editor/render/md_draw_ir.spl`
  projects TUI lines into the same `DrawIrComposition` the GUI dispatches, making
  the TUI lane GPU-offloadable like the GUI.
- **Two distinct font lanes.** Generated vector/bitmap glyph preparation can
  use checksum-gated GPU-offload payloads with CPU fallback. Separately,
  `Engine2D.load_font` selects a real TTF/OTF through the CPU `spl_fonts`
  owner, caches glyph alpha, builds one tight payload, and composites it on the
  selected drawing backend. Engine2D's unspecified default remains backend
  bitmap text; browser candidates are selected by the current font-provider
  policy rather than a separate GUI default.
  Trusted local paths use UTF-8 bytes. The selected native face/layout remains
  one serialized process-global singleton until concurrent owned handles are required.
- **MD WYSIWYG wired end-to-end** via `app/office/md_wysiwyg_{ppm,gui}.spl`.
- **Other 2D APIs share the SIMD-CPU/GPU interface via additive bridges** —
  `engine2d/bridge_game2d.spl`, `skia/bridge/engine2d_bridge.spl`,
  `engine2d/bridge_drawing_compositor.spl` dispatch game2d / skia / compositor
  primitives onto the shared `RenderBackend` `Engine2D` lanes (proven painting
  through `cpu_simd` and `software`). The rich draw surfaces are kept; only the
  backend interface is shared. Full primitive coverage is incremental follow-up.
- **Deliberately NOT done** (over-engineering guard): the ~5100-line web layout
  engine was not relocated into `common`.
