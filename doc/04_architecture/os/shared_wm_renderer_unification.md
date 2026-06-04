# Shared WM Renderer Unification Architecture

Date: 2026-05-29

## Status

Current implementation is a staged unification. The shared web render API and Engine2D backend files exist; WM service/core convergence remains the main architectural gap.

## Concrete API Files

- Web render contract: `src/lib/common/ui/web_render_api.spl`
- UI backend trait: `src/lib/common/ui/backend.spl`
- Surface registry: `src/lib/common/ui/window_surface_registry.spl`
- Web adapter: `src/app/ui.web/backend.spl`
- Electron adapter: `src/app/ui.electron/backend.spl`
- Tauri adapter: `src/app/ui.tauri/backend.spl`
- Host window command serialization and bridge bundle: `src/lib/common/ui/web_render_api.spl::WebRenderHostWindowCommand` and `web_render_transport_bundle(...)`, with compatibility wrapper in `src/app/ui.web/host_adapter_contract.spl`
- Engine2D backend trait: `src/lib/gc_async_mut/gpu/engine2d/backend.spl`
- Engine2D concrete backends: `backend_cpu.spl`, `backend_metal.spl`, `backend_cuda.spl`
- SimpleOS WM service/core: `src/os/services/wm/wm_service.spl`, `src/os/compositor/wm_core.spl`
- SimpleOS web window rendering adapter: `src/os/compositor/simple_web_window_renderer.spl`

## Boundaries

`common.ui.backend` and `doc/04_architecture/ui/shared_ui_contract.md` define the
semantic UI layer above transport. Native TUI, pure Simple GUI/web, Electron,
Tauri, and headless adapters may use different event loops and IPC, but they
must expose the same semantic widget tree, command vocabulary, focus state,
capability vocabulary, and read-after-write behavior before rendering. HTTP
`/api/test` remains the stable protocol only for Web and TUI-Web; staged
surfaces participate through adapter helpers until they grow protocol endpoints.

`common.ui.web_render_api` owns web render request, artifact, target capability, IPC JSON, host-window command JSON, snapshot envelopes, patch envelopes, input envelopes, and optional pixel-output representation. Platform adapters may own transport and native process details, but they must not invent incompatible render payloads. Host-native web surfaces are classified in `common.ui.window_surface_registry`; Electron and Tauri are both native-host surface kinds.

`WebRenderTransportBundle` is the common bridge proof for webview-style hosts.
It serializes render, input, snapshot, patch, and host-window command payloads
from the same request/command contract. Electron and Tauri adapter tests compare
their helper output to this bundle, so Chromium-webview access is shared through
`common.ui.web_render_api` while the native host process remains adapter-owned.

The SimpleOS web-window adapter exposes its app surfaces as `WebRenderRequest` values and its rasterized compositor payloads as `WebRenderArtifact` pixel artifacts. Host WM renderer-name reporting uses `WEB_RENDER_TARGET_SIMPLE_WEB` from the same common API instead of local string literals.

Pure Simple GUI/web follows the layered path:

```text
semantic UI tree
  -> shared web render request/artifact
  -> pure Simple web renderer
  -> Engine2D RenderBackend when pixels or captures are requested
```

Compatibility fixtures and recognized-site shortcuts are allowed only as
compatibility paths. They must not be counted as proof that the general Simple
web renderer path is Engine2D-backed.

Host-native surfaces are not a competing web renderer. They are an adapter
boundary for platform windows, input capture, and process/window integration.
When host WM content is web-rendered, Browser, Electron, and Tauri host handles
report `WEB_RENDER_TARGET_SIMPLE_WEB` and use the Simple Web content renderer.
Native host effects may remain in `HostCompositor`/backend-specific adapters,
but they must not introduce a separate web-render payload shape for SimpleOS app
content. `create_web_window` actions materialize a `WebRenderRequest` surface
through `wm_action_web_window_request(...)`; platform-native window management
stays below that shared web-render boundary.

`std.gpu.engine2d.backend.RenderBackend` owns the primitive 2D draw surface. Hardware-specific backends may mirror to software for readable pixels, but unavailable hardware must be represented through typed probe state instead of silent success. CUDA uses the shared `gc_async_mut` `CudaSession` entry point and now carries PTX clear, filled-rect, outline-rect, image, and gradient kernels plus launch/readback wiring. It only reports initialized after a hardware self-test proves the kernel path produces correct pixels.

WM common logic belongs below host and SimpleOS adapters. Host-only process/window effects stay adapter-private; lifecycle decisions for create, focus, move, resize, minimize, restore, close, update-tree, and input routing belong in the shared service/core layer. The host entry imports `os.services.wm.wm_service.WmService` for lifecycle state instead of defining a local service authority; bridge requests and pointer-driven drag/resize become shared `WmAction` lifecycle operations before they mutate host-native compositor state. SimpleOS remote create, create-web, destroy, focus, resize, move, set-title, minimize, maximize, restore, and update-tree compositor mutation now route through the shared `apply_wm_action_to_compositor(...)` helper. Shared remote update-tree materialization lives in `wm_action_remote_tree(...)`; shell-only launcher accounting, owner registry changes, IPC replies, and logs remain in `DesktopShell`.

Pointer move, left-button, resize-grip, and taskbar-hit behavior now use
`wm_lifecycle_pointer_move(...)`, `wm_lifecycle_left_button(...)`, and
`wm_lifecycle_hit_taskbar(...)` from `wm_action_applier.spl`. The hosted WM
entry still owns actual host window coordinates and launch bookkeeping, but the
state transitions are shared with the SimpleOS compositor path.

`HostCompositor` is not a second WM authority. It is the adapter-local
projection of host-native windows and event state into the shared lifecycle
model. Host bridge requests become `WmAction` values through
`wm_action_from_bridge_request(...)`, lifecycle mutations run through
`apply_wm_action_to_lifecycle_windows(...)`, and host mouse move/button input
runs through the same pointer helpers used by the shared WM tests. The adapter
may own native handles, process launch bookkeeping, failure-window presentation,
and framebuffer presentation because those are platform effects; it must not
own separate create/focus/move/resize/minimize/restore/destroy rules.

## Baremetal Overlay Boundary

The SimpleOS baremetal desktop overlay is an explicit adapter-private chrome
boundary, not a WM surface source. It draws taskbar, launcher, process panel,
and boot-demo window chrome through `CompositorBackend` so it shares the same
primitive 2D rendering API as host and SimpleOS compositor paths. It deliberately
does not materialize these overlay elements as `WidgetNode`/`UITree` compositor
surfaces in the baremetal lane because the widget builder DSL is not a safe boot
dependency there.

This boundary is part of the architecture, not an untracked workaround:

- WM-owned application windows, remote trees, create-web surfaces, focus, move,
  resize, minimize, restore, title, and destroy continue through shared
  `WmAction`/`apply_wm_action_to_compositor(...)` paths.
- Baremetal shell chrome remains shell-owned immediate-mode overlay state until
  the WidgetNode DSL has a verified baremetal-safe surface materialization path.
- The overlay may call only `CompositorBackend` draw primitives and must not
  depend on raw `Engine2D` APIs. `BaremetalEngine2dOverlayBackend` is the local
  adapter from the shared compositor contract to the boot Engine2D instance.
- `test/01_unit/os/desktop/shell_baremetal_backend_spec.spl` is the guardrail for
  this boundary: it proves `_draw_baremetal_overlay(...)` accepts a generic
  `CompositorBackend` and renders without requiring raw Engine2D access.

## Qt Size Baseline

The Qt comparison is an optional external baseline. `scripts/check/check-qt-gui-size-baseline.shs` records a report even when Qt development files are absent. It records both sides separately: the smallest measured Simple Web artifact from the web baremetal audit and the Qt minimal GUI artifact when Qt development files are available. It also records Qt discovery state for pkg-config, qmake, cmake, and c++. `comparison_status=unavailable` is evidence that the equal-or-better size claim could not be proven locally, not a failure of the Simple renderer verification path.

The GTK size/speed harness in `scripts/check/check-gtk-gui-size-speed-baseline.shs` belongs to the HTML/CSS binary-cache milestone. It measures Simple render-loop cost, static-cache hits, prepared `SWBC1` reuse, retained command payload bytes, and GTK availability separately from this WM-level Qt comparison.

## Verification

Focused verification should cover:

- `test/01_unit/app/ui/web_render_backend_api_spec.spl`
- semantic UI adapter conformance specs across TUI/Web/Electron/Tauri/headless
- `test/01_unit/app/ui/backend_matrix_spec.spl`
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/*backend*_spec.spl`
- `test/02_integration/rendering/cuda_strict_spec.spl`
- `test/01_unit/os/compositor/*wm*_spec.spl`
- `scripts/check/check-qt-gui-size-baseline.shs`
