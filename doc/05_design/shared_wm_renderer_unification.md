# Shared WM Renderer Unification Design

Date: 2026-05-29

## Design Scope

This slice documents the current concrete API files and the optional Qt size baseline behavior. It does not change renderer implementation files.

## Web Render API

`src/lib/common/ui/web_render_api.spl` is the canonical web render API. `WebRenderRequest` carries target, surface, HTML body, CSS, JS, viewport, and optional pixel-output intent. `WebRenderArtifact` carries generated HTML, body HTML, IPC JSON, optional pixels, and capability summary.

`WebRenderSnapshotEnvelope`, `WebRenderPatchEnvelope`, and `WebRenderInputEnvelope` define the shared renderer-neutral wire shape for state snapshots, incremental patch delivery, and user input events. These are transport envelopes: backend adapters can still own how stdin/stdout, web sockets, WebView messages, or framebuffer event queues move the JSON, but the payload fields stay common.

Adapters use the API as follows:

- `src/app/ui.web/backend.spl` renders Simple Web body/full-page output.
- `src/app/ui.electron/backend.spl` renders Electron HTML and IPC JSON through the shared artifact builder.
- `src/app/ui.tauri/backend.spl` renders Tauri HTML and IPC JSON through the shared artifact builder.
- `src/os/compositor/simple_web_window_renderer.spl` exposes WM app content through `WebRenderRequest` and blits `WebRenderArtifact.pixels`.
- `src/os/compositor/host_compositor_entry.spl` reports the shared `WEB_RENDER_TARGET_SIMPLE_WEB` target for host and SimpleOS framebuffer paths.
- Pure Simple browser participation is verified by `test/unit/app/ui/web_render_backend_api_spec.spl`.

Host native window command JSON uses `WebRenderHostWindowCommand` and `web_render_host_window_command_to_json` in `src/lib/common/ui/web_render_api.spl`. `src/app/ui.web/host_adapter_contract.spl` keeps its existing `HostWindowCommand` wrapper for callers and delegates serialization to the common API.

## Engine2D API

`src/lib/gc_async_mut/gpu/engine2d/backend.spl::RenderBackend` is the primitive draw contract. CPU, Metal, and CUDA concrete files must expose the same surface. CUDA uses an explicit `CudaSession` initialization hook so it can share the broader `gc_async_mut` CUDA context model. Its clear/filled-rect PTX and launch/readback path must remain capability-gated until a hardware self-test proves correct pixels. Tests must reject any path that claims CUDA rendered by silently falling back to CPU or by marking unverified kernels usable.

## WM API

`src/os/services/wm/wm_service.spl` and `src/os/compositor/wm_core.spl` are the shared WM authority targets. `src/os/compositor/host_compositor_entry.spl` now uses the real `WmService` as its lifecycle handle and converts host bridge messages plus pointer-driven drag/resize into shared `WmAction` lifecycle operations. `src/os/compositor/simple_web_window_renderer.spl` is the SimpleOS adapter that turns common web render requests into compositor pixels. Remaining host WM work should keep moving host-native input/surface policy into shared WM paths and keep platform effects below the adapter boundary.

## Size Baseline Design

`scripts/check-qt-gui-size-baseline.shs` writes `doc/09_report/qt_gui_size_baseline_<date>.md`. The report must include command, artifact paths, size fields, availability, the smallest measured Simple Web artifact from the web baremetal audit, and the comparison status. When Qt is missing, the report must say the baseline is unavailable and keep `comparison_status=unavailable`; it must not claim equal-or-better until both artifacts are measured.

## Error Handling

- Missing Qt: report `qt_build=unavailable` and `comparison_status=unavailable`; do not fail the script.
- Missing Simple web report: record Simple artifact as unavailable in the Qt report; rely on the web baremetal audit script for that side.
- Missing CUDA runtime/device/kernels or unverified CUDA kernel readback: typed unavailable or failed probe; no silent success.
