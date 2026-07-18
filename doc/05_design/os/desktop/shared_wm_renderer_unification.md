# Shared WM Renderer Unification Design

Date: 2026-05-29

## Design Scope

This slice documents the current concrete API files and the optional Qt size baseline behavior. It does not change renderer implementation files.

## Semantic UI API

The shared UI contract is semantic first. Each UI adapter converts application
state into the same widget tree and command vocabulary before transport-specific
serialization:

- Native TUI maps terminal widgets and key events to semantic widget IDs,
  focus, enabled/selected state, and commands.
- Pure Simple GUI/web maps semantic state to `WebRenderRequest` artifacts and
  then to Simple web renderer output.
- Electron and Tauri consume the same render/snapshot/patch/input envelopes as
  Web, while keeping IPC/WebView plumbing adapter-private.
- Headless exposes the same semantic state for tests without rendering pixels.

Design rule: backend-specific transport code may change delivery shape, but it
may not change widget kind values, focus semantics, command meanings,
capability names, or read-after-write behavior.

Code owner: `src/lib/common/ui/semantic_contract.spl`.

It defines the first S1/S2 facade over the existing UI access snapshot model:

- `SEMANTIC_UI_PROTOCOL_VERSION`;
- `SemanticElementInfo` matching `ElementInfo`;
- `SemanticUiStateInfo` matching `UIStateInfo`;
- `SemanticUiCommand` for click, type, submit, focus, key, resize, drag, and
  named action;
- `SemanticUiDispatchResult` with ok/error, affected element, and reason;
- `SemanticUiSnapshot` containing state, elements, capabilities, and optional
  capture metadata.

`RenderBackend` remains a rendering adapter interface. It can carry semantic
snapshots later, but it must not be treated as the semantic contract until these
typed structures and adapter tests exist.

## Web Render API

`src/lib/common/ui/web_render_api.spl` is the canonical web render API. `WebRenderRequest` carries target, surface, HTML body, CSS, JS, viewport, and optional pixel-output intent. `WebRenderArtifact` carries generated HTML, body HTML, IPC JSON, optional pixels, and capability summary.

`WebRenderSnapshotEnvelope`, `WebRenderPatchEnvelope`, and `WebRenderInputEnvelope` define the shared renderer-neutral wire shape for state snapshots, incremental patch delivery, and user input events. These are transport envelopes: backend adapters can still own how stdin/stdout, web sockets, WebView messages, or framebuffer event queues move the JSON, but the payload fields stay common.

Adapters use the API as follows:

- `src/app/ui.web/backend.spl` renders Simple Web body/full-page output.
- `src/app/ui.electron/backend.spl` renders Electron HTML and IPC JSON through the shared artifact builder.
- `src/app/ui.tauri/backend.spl` renders Tauri HTML and IPC JSON through the shared artifact builder.
- `src/app/ui.web/backend.spl`, `src/app/ui.electron/backend.spl`, and `src/app/ui.tauri/backend.spl` expose adapter helpers for common snapshot, patch, and input envelopes. Electron and Tauri standalone and async render loops now emit render IPC from common `WebRenderRequest` artifacts. `src/app/ui.ipc/async_handler.spl` preserves complete common render IPC JSON and wraps legacy raw HTML only for compatibility. `src/app/ui.web/server.spl` keeps its legacy `type:"render"` WebSocket frame shape but derives the body through `WebRenderRequest`/`web_render_body_html` and carries the `simple_web` target. `src/app/ui.web/web_runtime_adapter.spl` sends live snapshot and patch payloads through those common envelopes; the browser WebSocket boundary unwraps them before calling the retained renderer. Electron and Tauri snapshot/patch helper output is covered by behavioral equality tests against the shared web backend helpers; remaining verification is end-to-end native host WebView delivery.
- `src/os/compositor/simple_web_window_renderer.spl` exposes WM app content through `WebRenderRequest` and blits `WebRenderArtifact.pixels`.
- `src/os/compositor/host_compositor_entry.spl` reports the shared `WEB_RENDER_TARGET_SIMPLE_WEB` target for host and SimpleOS framebuffer paths.
- Pure Simple browser participation is verified by `test/01_unit/app/ui/web_render_backend_api_spec.spl`.

Pure Simple GUI renderer path:

1. Build semantic UI state through the shared UI backend contract.
2. Convert semantic state into `WebRenderRequest`/snapshot/patch/input
   artifacts.
3. Render through the pure Simple web renderer.
4. Use Engine2D `RenderBackend` for pixel output, capture, and equality
   evidence when requested.
5. Report fixture-only or recognized-site shortcuts separately from general
   Engine2D-backed renderer evidence.

Host-native surface and input capture code is adapter-private. It is allowed to
own native window handles, host process effects, and backend-specific event
plumbing, but not SimpleOS web content serialization. The shared web renderer
boundary is:

- Host WM content renderer names for Browser, Electron, and Tauri resolve to
  `WEB_RENDER_TARGET_SIMPLE_WEB`.
- `create_web_window` maps to a `WebRenderRequest` with target `simple_web`,
  a stable `web_window_<id>` surface id, pixel output requested, and the same
  URL-derived body helper used by SimpleOS.
- SimpleOS web app content uses `simple_web_window_renderer.spl` to produce the
  same request/artifact shape before blitting pixels to `CompositorBackend`.
- Native host surfaces remain outside this web-render API because they are
  platform/windowing effects, not web content renderers.

Host native window command JSON uses `WebRenderHostWindowCommand` and `web_render_host_window_command_to_json` in `src/lib/common/ui/web_render_api.spl`. `src/app/ui.web/host_adapter_contract.spl` keeps its existing `HostWindowCommand` wrapper for callers and delegates serialization to the common API.

## Engine2D API

`src/lib/gc_async_mut/gpu/engine2d/backend.spl::RenderBackend` is the primitive draw contract. CPU, Metal, and CUDA concrete files must expose the same surface. CUDA uses an explicit `CudaSession` initialization hook so it can share the broader `gc_async_mut` CUDA context model. Its clear, filled-rect, and outline-rect PTX launch/readback paths remain capability-gated by a hardware self-test that must prove correct pixels before CUDA is marked initialized. Tests must reject any path that claims CUDA rendered by silently falling back to CPU or by marking unverified kernels usable.

## WM API

`src/os/services/wm/wm_service.spl` and `src/os/compositor/wm_core.spl` are the shared WM authority targets. `src/os/compositor/host_compositor_entry.spl` now uses the real `WmService` as its lifecycle handle and converts host bridge messages plus pointer-driven drag/resize into shared `WmAction` lifecycle operations. `src/os/desktop/shell.spl` routes remote create, create-web, destroy, focus, resize, move, set-title, minimize, maximize, restore, and update-tree compositor mutation through `apply_wm_action_to_compositor(...)` and keeps shell-owned side effects local. `src/os/compositor/wm_action_applier.spl` owns the shared remote update-tree materialization and the lifecycle/pointer helpers used by both `HostCompositor` and the SimpleOS QEMU WM evidence path. `src/os/compositor/simple_web_window_renderer.spl` remains the richer host-capable Simple Web content renderer; `src/os/compositor/shared_mdi_framebuffer_scene.spl` is the shared framebuffer-safe chrome/layout/content renderer for host direct-draw chrome and QEMU evidence. Remaining divergence is adapter-owned: host cached web pixels and native event/process plumbing, QEMU framebuffer backend/config, and the QEMU entry's direct use of shared scene/pointer helpers instead of constructing `SimpleOsGuiAdapter`.

### Resolution And DPI Contract

WM performance work must preserve output quality. A change is not an acceptable
optimization if it lowers logical size, physical pixel size, DPI, text
readability, theme fidelity, animation semantics, or renderer feature coverage.
Host and SimpleOS WM targets must be designed for 8K-class desktops and higher
(7680x4320 and above) and for at least 300 DPI content. Evidence may use smaller
smoke fixtures only when explicitly labeled as smoke coverage; completion and
performance claims must keep the requested target resolution and pixel density.

Allowed optimizations remove real overhead: avoiding duplicate full-frame
copies, avoiding per-pixel FFI, using retained/dirty rendering, batching spans,
and sharing renderer/lifecycle code. Forbidden optimizations include shrinking
the framebuffer, rendering fewer pixels than requested, replacing text with
markers, bypassing CSS/theme application when the lane claims CSS coverage, or
using hardcoded/dummy WM rectangles as completion evidence.

The host adapter uses `HostedWindow` only as the platform projection of
`WmLifecycleWindowState`. Conversion helpers
`host_windows_to_lifecycle_state(...)` and
`host_windows_from_lifecycle_state(...)` define the boundary. The only allowed
host-side lifecycle entry points are:

- bridge request conversion through `wm_action_from_bridge_request(...)`;
- lifecycle application through `host_compositor_apply_lifecycle_action(...)`,
  which delegates to `apply_wm_action_to_lifecycle_windows(...)`;
- pointer motion through `host_compositor_pointer_move(...)`, which delegates to
  `wm_lifecycle_pointer_move(...)`;
- left-button state through `host_compositor_left_button(...)`, which delegates
  to `wm_lifecycle_left_button(...)`;
- taskbar hit testing through `wm_lifecycle_hit_taskbar(...)`.

Host process launch failure windows, native backend construction, event-loop
pumping, and presentation remain adapter-owned side effects. They are not WM
policy and must not duplicate lifecycle rules.

### 2026-07-06 QEMU Render Path

`shared_mdi_framebuffer_scene.spl` is the shared desktop renderer used by the
x86_64 QEMU WM evidence path. Its freestanding content path draws Simple
Web-style app areas directly through `CompositorBackend`, using compiled colors
and shared MDI surface data only. This keeps the baremetal lane free of
host-only `rt_file_exists`, theme-package file reads, host env probes, and
runtime web-render queues.

The host adapter is allowed to render window content with the richer
`simple_web_window_renderer.spl` cached pixel path because host file/env/runtime
facades are available there. The design boundary is source ownership, not byte
identity of every presentation backend: shared WM chrome/layout/content source
is common, while host/native and SimpleOS differ only in adapter effects and
backend configuration.

`SimpleOsGuiAdapter` is the tested SimpleOS-style bridge projection over
`HostCompositor`: `deliver_bridge_request(...)` converts compositor bridge
methods into shared WM lifecycle actions, `deliver_pointer_move(...)` and
`deliver_left_button(...)` use the same pointer helpers, and
`render_framebuffer_frame(...)` presents through the shared host compositor
render path. The x86_64 QEMU evidence entry is deliberately thinner than that
host-side wrapper because the baremetal lane has no host window/event loop, but
it still enters the same Simple GUI internal-window scene before framebuffer
drawing: lifecycle windows are converted by
`render_shared_mdi_framebuffer_scene_for_lifecycle_windows(...)` to render
windows, then to `simple_gui_internal_window_scene(...)` through
`render_shared_mdi_framebuffer_scene_for_windows(...)` and
`render_shared_mdi_framebuffer_scene_for_simple_gui_scene(...)`. This is the
required shared rendering contract; host and SimpleOS may differ in adapter
effects and backend configuration, not in WM policy or internal-window scene
shape.

## Baremetal Overlay Design Boundary

The x86 baremetal desktop overlay is not a WM-owned surface. It is boot-shell
chrome rendered after shared compositor state through `CompositorBackend`.
`src/os/desktop/shell_baremetal.spl` owns this immediate-mode overlay because
the `WidgetNode` DSL and full surface materialization path are not verified as
safe boot dependencies in the baremetal lane.

The implementation rule is narrow: shell overlay drawing may use
`CompositorBackend` primitives only. It must not call raw `Engine2D` directly,
and it must not duplicate WM lifecycle state for app windows. When the boot lane
can safely materialize WidgetNode surfaces, this boundary can be revisited; until
then, shell-owned chrome is the explicit non-WM boundary and application/window
state remains in the shared WM path.

## Size Baseline Design

`scripts/check/check-qt-gui-size-baseline.shs` writes `doc/09_report/qt_gui_size_baseline_<date>.md`. The report must include command, artifact paths, size fields, availability, Qt discovery state, the smallest measured Simple Web artifact from the web baremetal audit, and the comparison status. When Qt is missing, the report must say the baseline is unavailable and keep `comparison_status=unavailable`; it must not claim equal-or-better until both artifacts are measured.

## Error Handling

- Missing Qt: report `qt_build=unavailable` and `comparison_status=unavailable`; do not fail the script.
- Missing Simple web report: record Simple artifact as unavailable in the Qt report; rely on the web baremetal audit script for that side.
- Missing CUDA runtime/device/kernels or unverified CUDA kernel readback: typed unavailable or failed probe; no silent success.
- Missing semantic adapter support: report `semantic_adapter_unavailable` for
  that surface; do not treat a transport-specific render pass as semantic UI
  conformance.
