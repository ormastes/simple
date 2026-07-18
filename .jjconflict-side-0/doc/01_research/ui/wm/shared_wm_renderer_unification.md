<!-- codex-research -->
# Shared WM Renderer Unification — Local Research

Date: 2026-05-29

## Objective Checked

User objective: make Electron, Tauri, and pure Simple web renderer share one web render API; make CUDA, Metal, and CPU 2D renderers share one 2D rendering API; make host WM and SimpleOS WM share logic and use the same web renderer and 2D engine APIs.

## Verdict

The requested end state is not true yet. The repo has several converged surfaces, but the web renderer, 2D engine, and WM service layers are still partially parallel.

## Evidence

### Web renderer surfaces

- `src/app/ui.web/backend.spl:6` imports `common.ui.backend.RenderBackend`, and `WebBackend` implements `render`, `render_html`, `poll_event`, capabilities, viewport, and `backend_name` at `src/app/ui.web/backend.spl:39`, `:44`, `:49`, `:55`, `:75`, and `:83`.
- `src/app/ui.electron/backend.spl:6` imports the same UI backend trait. Electron renders HTML then emits stdout IPC through `build_ipc_render` at `src/app/ui.electron/backend.spl:40-46`, polls stdin IPC at `:54-60`, and has Electron-only window commands at `:119-129`.
- `src/app/ui.tauri/backend.spl:7` imports the same UI backend trait. Tauri renders HTML then emits IPC through `build_ipc_render` at `src/app/ui.tauri/backend.spl:51-57`, polls stdin IPC at `:65-71`, and has capability checks for native features at `:111-127`.
- The shared host adapter contract names SimpleWeb and ElectronWeb only at `src/app/ui.web/host_adapter_contract.spl:3`. It defines `HostWindowCommand` and JSON framing at `:11-35`, but not a renderer-neutral API that includes Tauri and pure Simple browser pixels.
- The surface registry has `Legacy`, `SimpleWeb`, `Electron`, and `Headless` constants at `src/lib/common/ui/window_surface_registry.spl:8-11`; there is no `Tauri` kind. Native host detection currently returns true only for Electron at `:13-15`.

Conclusion: Electron, Tauri, and web share conventions and some helper modules, but there is no explicit `WebRenderApi` contract covering HTML render, snapshot/patch render, input, host window commands, capability reporting, and optional pixel output.

### 2D renderer surfaces

- The main 2D drawing contract is `std.gpu.engine2d.backend.RenderBackend` at `src/lib/gc_async_mut/gpu/engine2d/backend.spl:3-25`; it includes lifecycle, drawing primitives, clip/mask, present, readback, and dimensions.
- `Engine2D` states that all drawing delegates through `RenderBackend` at `src/lib/gc_async_mut/gpu/engine2d/engine.spl:37-42`.
- Backend creation includes CUDA, Metal, software, and CPU paths at `src/lib/gc_async_mut/gpu/engine2d/engine.spl:102-153`, and auto-detection prioritizes CUDA, ROCm, Metal, then other GPU backends before software at `:240-289`.
- CPU conforms through `CpuBackend` delegating to software rendering (`src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl:16`).
- Metal has the trait shape through `backend_metal.spl`, but current local research found it mirror-backed rather than complete native primitive dispatch.
- CUDA is imported by `src/lib/gc_async_mut/gpu/engine2d/engine.spl:19` and documented in `mod.spl`, but `src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl` is absent.
- A second session-oriented API exists in `src/lib/gc_async_mut/gpu/engine2d/engine2d_api.spl` with a smaller `fill`, `blit`, `present`, `read_pixels` surface, so there are two API shapes to reconcile.

Conclusion: CPU and Metal can be made to share the existing `RenderBackend` contract, but CUDA is missing and session-level APIs need convergence with the primitive backend trait.

### WM sharing

- `doc/04_architecture/os/shared_wm_stack.md` already states the desired architecture: host UI shells and SimpleOS run the same headless `WmService` + `Compositor` with no duplication.
- `src/os/compositor/display_backend.spl:9-19` defines `CompositorBackend`, the current compositor rendering interface.
- `src/os/compositor/host_compositor_entry.spl:13-28` exposes host backend selection and `HostWmConfig`.
- `src/os/compositor/host_compositor_entry.spl:164-178` renders hosted windows through `render_simple_web_app_content`, so host content already goes through the Simple web renderer path in one place.
- However, `src/os/compositor/host_compositor_entry.spl:50-57` defines a local minimal `WmService` rather than importing the real service from `src/os/services/wm/wm_service.spl`.
- `src/os/compositor/host_compositor_entry.spl:379-386` and `:408-410` explicitly reject TUI host compositor startup.
- SimpleOS has a direct Engine2D overlay path noted by local agent research at `src/os/desktop/shell.spl:613-617`, which bypasses the compositor abstraction.

Conclusion: the architectural intent exists, but current implementation does not yet prove a single WM service/logic path for host and SimpleOS.

## Gaps To Plan

1. Add an explicit shared web render API in `src/lib/common/ui/` or `src/app/ui.web/` and adapt Web, Electron, Tauri, and pure Simple browser rendering to it.
2. Add or repair `backend_cuda.spl` so CUDA participates in the same `RenderBackend` contract as CPU and Metal.
3. Decide how the session-level `engine2d_api.spl` surface composes with or wraps the primitive `RenderBackend` trait.
4. Replace the host local `WmService` shim with the real WM service or extract the duplicated host logic into a shared WM core that both host and SimpleOS use.
5. Route SimpleOS direct Engine2D overlay drawing through the compositor or a documented shared 2D engine adapter.
6. Add requirement options and ask for selection before final requirements.
