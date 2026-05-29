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
- Host window command serialization: `src/lib/common/ui/web_render_api.spl::WebRenderHostWindowCommand`, with compatibility wrapper in `src/app/ui.web/host_adapter_contract.spl`
- Engine2D backend trait: `src/lib/gc_async_mut/gpu/engine2d/backend.spl`
- Engine2D concrete backends: `backend_cpu.spl`, `backend_metal.spl`, `backend_cuda.spl`
- SimpleOS WM service/core: `src/os/services/wm/wm_service.spl`, `src/os/compositor/wm_core.spl`
- SimpleOS web window rendering adapter: `src/os/compositor/simple_web_window_renderer.spl`

## Boundaries

`common.ui.web_render_api` owns web render request, artifact, target capability, IPC JSON, host-window command JSON, snapshot envelopes, patch envelopes, input envelopes, and optional pixel-output representation. Platform adapters may own transport and native process details, but they must not invent incompatible render payloads.

The SimpleOS web-window adapter exposes its app surfaces as `WebRenderRequest` values and its rasterized compositor payloads as `WebRenderArtifact` pixel artifacts. Host WM renderer-name reporting uses `WEB_RENDER_TARGET_SIMPLE_WEB` from the same common API instead of local string literals.

`std.gpu.engine2d.backend.RenderBackend` owns the primitive 2D draw surface. Hardware-specific backends may mirror to software for readable pixels, but unavailable hardware must be represented through typed probe state instead of silent success. CUDA uses the shared `gc_async_mut` `CudaSession` entry point and now carries PTX clear/filled-rect kernels plus launch/readback wiring, but it remains unavailable until a hardware self-test proves those kernels produce correct pixels.

WM common logic belongs below host and SimpleOS adapters. Host-only process/window effects stay adapter-private; lifecycle decisions for create, focus, move, resize, minimize, restore, close, and input routing belong in the shared service/core layer. The host entry imports `os.services.wm.wm_service.WmService` for lifecycle state instead of defining a local service authority; bridge requests and pointer-driven drag/resize become shared `WmAction` lifecycle operations before they mutate host-native compositor state.

## Qt Size Baseline

The Qt comparison is an optional external baseline. `scripts/check-qt-gui-size-baseline.shs` records a report even when Qt development files are absent. It now records both sides separately: the smallest measured Simple Web artifact from the web baremetal audit and the Qt minimal GUI artifact when Qt development files are available. `comparison_status=unavailable` is evidence that the equal-or-better size claim could not be proven locally, not a failure of the Simple renderer verification path.

## Verification

Focused verification should cover:

- `test/unit/app/ui/web_render_backend_api_spec.spl`
- `test/unit/app/ui/backend_matrix_spec.spl`
- `test/unit/lib/gpu/engine2d/*backend*_spec.spl`
- `test/unit/os/compositor/*wm*_spec.spl`
- `scripts/check-qt-gui-size-baseline.shs`
