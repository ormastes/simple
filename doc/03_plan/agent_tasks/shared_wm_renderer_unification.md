# Shared WM Renderer Unification — Plan

Date: 2026-05-29

## Current Status

Local agent research found the requested end state is incomplete. Existing contracts cover parts of the goal, but there is no single web render API for Web/Electron/Tauri/pure Simple renderer, CUDA lacks a concrete Engine2D backend file, and host WM still has local service logic that conflicts with the shared WM architecture.

## Recommended Path

Recommended selection: Feature Option C with NFR Option 3 if the goal is to make the complete objective true. If the next turn should be lower risk, choose Feature Option B with NFR Option 2 first, then follow with WM service unification.

## Implementation Phases

1. Finalize requirements after user selection.
2. Design `WebRenderApi`:
   - Shared request/response types for HTML render, snapshot/patch render, input forwarding, host window commands, capabilities, and optional pixel output.
   - Add `UI_SURFACE_KIND_TAURI` or replace surface-kind constants with a host-renderer capability model.
   - Move Electron/Tauri duplicate `build_ipc_render` usage behind the shared API.
3. Design Engine2D API convergence:
   - Treat `src/lib/gc_async_mut/gpu/engine2d/backend.spl::RenderBackend` as the mandatory primitive API.
   - Make session APIs wrap that trait instead of competing with it.
   - Add or restore `backend_cuda.spl`; verify CPU, Metal, and CUDA compile against the same trait.
4. Design WM logic sharing:
   - Remove or replace the local `WmService` in `host_compositor_entry.spl`.
   - Extract any host-only window list mechanics into adapter code below the real WM service/core.
   - Route SimpleOS direct overlay drawing through `CompositorBackend` or `Engine2dCompositorBackend`.
5. Add system tests:
   - Shared web render API parity across Web/Electron/Tauri/pure Simple.
   - Engine2D backend trait conformance for CPU/Metal/CUDA.
   - Host and SimpleOS WM behavior parity for window lifecycle and input routing.
6. Implement in staged patches:
   - Web API first.
   - 2D backend API second.
   - WM service sharing third.
7. Verify:
   - Run focused SPipe specs.
   - Run compiler/lib checks if shared library or compiler-facing imports change.
   - For WM/tooling hot paths, capture warm startup, representative latency, and RSS where applicable.

## Open Decisions

- Whether to use `src/lib/common/ui/web_render_api.spl` as the canonical web API location or keep it in `src/app/ui.web/render_api.spl`.
- Whether CUDA must be a real accelerated renderer in the first implementation or a capability-gated backend that returns unavailable without pretending to render.
- Whether host TUI is in scope for this goal or should remain an explicit unsupported backend while Web/Electron/Tauri/pure Simple are unified.
