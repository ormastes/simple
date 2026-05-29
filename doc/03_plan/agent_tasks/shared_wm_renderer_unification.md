# Shared WM Renderer Unification — Plan

Date: 2026-05-29

## Current Status

Local agent research found the requested end state is now partially implemented. Existing contracts cover the shared web render API in `src/lib/common/ui/web_render_api.spl`, concrete Web/Electron/Tauri consumers, and concrete CPU/Metal/CUDA Engine2D backend files. Remaining work is to keep the docs/specs aligned with those API files, prove pure Simple browser parity, and close any host WM versus SimpleOS WM service/core gaps.

## Recommended Path

Recommended selection: Feature Option C with NFR Option 3 if the goal is to make the complete objective true. If the next turn should be lower risk, choose Feature Option B with NFR Option 2 first, then follow with WM service unification.

## Implementation Phases

1. Finalize requirements after user selection.
2. Maintain shared web render API docs/specs:
   - Treat `src/lib/common/ui/web_render_api.spl` as the canonical request/artifact/capability API.
   - Keep Web/Electron/Tauri and pure Simple browser participation covered by one conformance spec.
   - Track host window command serialization separately in `src/app/ui.web/host_adapter_contract.spl`.
3. Maintain Engine2D API convergence:
   - Treat `src/lib/gc_async_mut/gpu/engine2d/backend.spl::RenderBackend` as the mandatory primitive API.
   - Make session APIs wrap that trait instead of competing with it.
   - Keep `backend_cpu.spl`, `backend_metal.spl`, and `backend_cuda.spl` aligned, with CUDA allowed to report typed unavailable capability.
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

- Whether `UI_SURFACE_KIND_TAURI` should be added or whether Tauri remains represented through capability policy without a distinct surface kind.
- Whether CUDA must become a real accelerated renderer in this feature or remain a capability-gated backend that returns unavailable without pretending to render.
- Whether host TUI is in scope for this goal or should remain an explicit unsupported backend while Web/Electron/Tauri/pure Simple are unified.
