# Shared WM Renderer Unification Design

Date: 2026-05-29

## Design Scope

This slice documents the current concrete API files and the optional Qt size baseline behavior. It does not change renderer implementation files.

## Web Render API

`src/lib/common/ui/web_render_api.spl` is the canonical web render API. `WebRenderRequest` carries target, surface, HTML body, CSS, JS, viewport, and optional pixel-output intent. `WebRenderArtifact` carries generated HTML, body HTML, IPC JSON, optional pixels, and capability summary.

Adapters use the API as follows:

- `src/app/ui.web/backend.spl` renders Simple Web body/full-page output.
- `src/app/ui.electron/backend.spl` renders Electron HTML and IPC JSON through the shared artifact builder.
- `src/app/ui.tauri/backend.spl` renders Tauri HTML and IPC JSON through the shared artifact builder.
- Pure Simple browser participation is verified by `test/unit/app/ui/web_render_backend_api_spec.spl`.

Host native window command JSON remains in `src/app/ui.web/host_adapter_contract.spl`; it is related to WM transport, not the render artifact itself.

## Engine2D API

`src/lib/gc_async_mut/gpu/engine2d/backend.spl::RenderBackend` is the primitive draw contract. CPU, Metal, and CUDA concrete files must expose the same surface. CUDA may return an unavailable probe when runtime, devices, or kernels are missing; tests must reject any path that claims CUDA rendered by silently falling back to CPU.

## WM API

`src/os/services/wm/wm_service.spl` and `src/os/compositor/wm_core.spl` are the shared WM authority targets. `src/os/compositor/simple_web_window_renderer.spl` is the SimpleOS adapter that turns web content into compositor pixels. Remaining host WM work should move lifecycle policy into this shared layer and keep host-only native effects below the adapter boundary.

## Size Baseline Design

`scripts/check-qt-gui-size-baseline.shs` writes `doc/09_report/qt_gui_size_baseline_<date>.md`. The report must include command, artifact paths, size fields, and availability. When Qt is missing, the report must say the baseline is optional/unavailable and verification must continue.

## Error Handling

- Missing Qt: report `qt_status=unavailable`; do not fail the script.
- Missing Simple web report: record Simple artifact as unavailable in the Qt report; rely on the web baremetal audit script for that side.
- Missing CUDA runtime/device/kernels: typed unavailable or failed probe; no silent success.
