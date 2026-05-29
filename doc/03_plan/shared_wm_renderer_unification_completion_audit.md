# Shared WM Renderer Unification — Completion Audit

Date: 2026-05-29

## Scope

This audit maps the active objective to current evidence. It is intentionally stricter than the current implementation state: uncertain or partial evidence is treated as incomplete.

## Requirement Matrix

| Objective requirement | Evidence needed for completion | Current evidence | Status |
|---|---|---|---|
| Electron, Tauri, and pure Simple web renderer share the same web render API interface | A single Simple API/trait/module imported by all three adapters, with tests proving the same request/response contract for HTML/snapshot/patch/input/capabilities/host-window operations and optional pixel output | `src/lib/common/ui/web_render_api.spl` exists and `ui.web`, `ui.electron`, and `ui.tauri` import it. `test/unit/app/ui/web_render_backend_api_spec.spl` covers those backends plus pure Simple browser artifact participation. Host window commands remain in `src/app/ui.web/host_adapter_contract.spl`, and surface registry still has no Tauri kind. | Partially complete |
| CUDA, Metal, and CPU 2D renderers share the same 2D rendering API interface | CPU, Metal, and CUDA backend files all implement `std.gpu.engine2d.backend.RenderBackend`; backend selection compiles; tests assert mandatory method parity and capability handling | `RenderBackend` exists in `src/lib/gc_async_mut/gpu/engine2d/backend.spl`; CPU, Metal, and CUDA concrete files exist. CUDA reports typed unavailable/failed probe states when runtime or render kernels are unavailable rather than claiming CPU fallback rendering. | Partially complete |
| Host WM and SimpleOS WM share logic | Host and SimpleOS import/use the same WM service/core for create/focus/move/resize/minimize/restore/close/input routing; no local host service shim duplicates WM authority | Architecture doc claims this, but `host_compositor_entry.spl` defines local minimal `WmService`. SimpleOS uses real WM service. | Contradicted |
| Host WM and SimpleOS WM use the same web renderer API | Host and SimpleOS web rendering path both call shared web render API, with tests for the same fixture | Host content calls `render_simple_web_app_content` in one path, but no common WebRenderApi exists for all host adapters and SimpleOS. | Incomplete |
| Host WM and SimpleOS WM use the same 2D engine API | Both paths render through `CompositorBackend`/`Engine2D RenderBackend` adapters and do not bypass with direct platform-specific overlay drawing | Compositor/Engine2D adapters exist, but local research found SimpleOS direct Engine2D overlay drawing bypasses compositor surfaces. | Incomplete |
| Research local with agents | Independent local explorer results for web renderer, 2D renderer, WM sharing, and artifact presence | Agents completed and findings were merged into `doc/01_research/local/shared_wm_renderer_unification.md`. | Complete |
| If not complete, plan | Requirement options, NFR options, and staged plan exist | Options and plan are present under `shared_wm_renderer_unification`. | Complete |

## Blocking Decisions Before Final Requirements

Repo process requires user selection before final requirements are written. The available choices are:

- Feature option: A, B, C, or D in `doc/02_requirements/feature/shared_wm_renderer_unification_options.md`.
- NFR option: 1, 2, or 3 in `doc/02_requirements/nfr/shared_wm_renderer_unification_options.md`.

Recommended for the full objective: Feature Option C plus NFR Option 3.

## Next Evidence To Produce After Selection

1. Final requirements:
   - `doc/02_requirements/feature/shared_wm_renderer_unification.md`
   - `doc/02_requirements/nfr/shared_wm_renderer_unification.md`
2. Architecture and design:
   - `doc/04_architecture/shared_wm_renderer_unification.md`
   - `doc/05_design/shared_wm_renderer_unification.md`
3. System tests:
   - web render API parity spec
   - Engine2D backend interface conformance spec
   - host/SimpleOS WM logic parity spec
4. Implementation evidence:
   - keep shared web render API imported by Web/Electron/Tauri/pure Simple renderer
   - keep concrete CUDA `RenderBackend` capability-gated until real kernels exist
   - host WM no longer owns a duplicate `WmService`
   - SimpleOS direct overlay path routed through shared rendering APIs or explicitly out of WM scope
