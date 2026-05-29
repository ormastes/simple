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

`common.ui.web_render_api` owns web render request, artifact, target capability, IPC JSON, host-window command JSON, snapshot envelopes, patch envelopes, input envelopes, and optional pixel-output representation. Platform adapters may own transport and native process details, but they must not invent incompatible render payloads. Host-native web surfaces are classified in `common.ui.window_surface_registry`; Electron and Tauri are both native-host surface kinds.

`WebRenderTransportBundle` is the common bridge proof for webview-style hosts.
It serializes render, input, snapshot, patch, and host-window command payloads
from the same request/command contract. Electron and Tauri adapter tests compare
their helper output to this bundle, so Chromium-webview access is shared through
`common.ui.web_render_api` while the native host process remains adapter-owned.

The SimpleOS web-window adapter exposes its app surfaces as `WebRenderRequest` values and its rasterized compositor payloads as `WebRenderArtifact` pixel artifacts. Host WM renderer-name reporting uses `WEB_RENDER_TARGET_SIMPLE_WEB` from the same common API instead of local string literals.

`std.gpu.engine2d.backend.RenderBackend` owns the primitive 2D draw surface. Hardware-specific backends may mirror to software for readable pixels, but unavailable hardware must be represented through typed probe state instead of silent success. CUDA uses the shared `gc_async_mut` `CudaSession` entry point and now carries PTX clear, filled-rect, outline-rect, image, and gradient kernels plus launch/readback wiring. It only reports initialized after a hardware self-test proves the kernel path produces correct pixels.

WM common logic belongs below host and SimpleOS adapters. Host-only process/window effects stay adapter-private; lifecycle decisions for create, focus, move, resize, minimize, restore, close, update-tree, and input routing belong in the shared service/core layer. The host entry imports `os.services.wm.wm_service.WmService` for lifecycle state instead of defining a local service authority; bridge requests and pointer-driven drag/resize become shared `WmAction` lifecycle operations before they mutate host-native compositor state. SimpleOS remote create, create-web, destroy, focus, resize, move, set-title, minimize, maximize, restore, and update-tree compositor mutation now route through the shared `apply_wm_action_to_compositor(...)` helper. Shared remote update-tree materialization lives in `wm_action_remote_tree(...)`; shell-only launcher accounting, owner registry changes, IPC replies, and logs remain in `DesktopShell`.

Pointer move, left-button, resize-grip, and taskbar-hit behavior now use
`wm_lifecycle_pointer_move(...)`, `wm_lifecycle_left_button(...)`, and
`wm_lifecycle_hit_taskbar(...)` from `wm_action_applier.spl`. The hosted WM
entry still owns actual host window coordinates and launch bookkeeping, but the
state transitions are shared with the SimpleOS compositor path.

## Qt Size Baseline

The Qt comparison is an optional external baseline. `scripts/check-qt-gui-size-baseline.shs` records a report even when Qt development files are absent. It records both sides separately: the smallest measured Simple Web artifact from the web baremetal audit and the Qt minimal GUI artifact when Qt development files are available. It also records Qt discovery state for pkg-config, qmake, cmake, and c++. `comparison_status=unavailable` is evidence that the equal-or-better size claim could not be proven locally, not a failure of the Simple renderer verification path.

The GTK size/speed harness in `scripts/check-gtk-gui-size-speed-baseline.shs` belongs to the HTML/CSS binary-cache milestone. It measures Simple render-loop cost, static-cache hits, prepared `SWBC1` reuse, retained command payload bytes, and GTK availability separately from this WM-level Qt comparison.

## Verification

Focused verification should cover:

- `test/unit/app/ui/web_render_backend_api_spec.spl`
- `test/unit/app/ui/backend_matrix_spec.spl`
- `test/unit/lib/gc_async_mut/gpu/engine2d/*backend*_spec.spl`
- `test/integration/rendering/cuda_strict_spec.spl`
- `test/unit/os/compositor/*wm*_spec.spl`
- `scripts/check-qt-gui-size-baseline.shs`
