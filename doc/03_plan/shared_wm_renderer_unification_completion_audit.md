# Shared WM Renderer Unification — Completion Audit

Date: 2026-05-29

## Scope

This audit maps the active objective to current evidence. It is intentionally stricter than the current implementation state: uncertain or partial evidence is treated as incomplete.

## Requirement Matrix

| Objective requirement | Evidence needed for completion | Current evidence | Status |
|---|---|---|---|
| Electron, Tauri, and pure Simple web renderer share the same web render API interface | A single Simple API/trait/module imported by all three adapters, with tests proving the same request/response contract for HTML/snapshot/patch/input/capabilities/host-window operations and optional pixel output | `src/lib/common/ui/web_render_api.spl` exists and `ui.web`, `ui.electron`, and `ui.tauri` import it. `test/unit/app/ui/web_render_backend_api_spec.spl` covers those backends plus pure Simple browser artifact participation. Host window command JSON delegates to `WebRenderHostWindowCommand`; snapshot, patch, and input wire payloads are represented by `WebRenderSnapshotEnvelope`, `WebRenderPatchEnvelope`, and `WebRenderInputEnvelope`, covered by `test/unit/lib/common/ui/web_render_api_spec.spl`. Pure Simple browser event queueing now records the common input envelope. Surface registry still has no Tauri kind, and Electron/Tauri/Web have not all been migrated to emit/consume the new envelopes directly. | Partially complete |
| CUDA, Metal, and CPU 2D renderers share the same 2D rendering API interface | CPU, Metal, and CUDA backend files all implement `std.gpu.engine2d.backend.RenderBackend`; backend selection compiles; tests assert mandatory method parity and capability handling | `RenderBackend` exists in `src/lib/gc_async_mut/gpu/engine2d/backend.spl`; CPU, Metal, and CUDA concrete files exist. CUDA now accepts an explicit `CudaSession`, includes PTX source and launch/readback wiring for `kernel_clear` and `kernel_draw_rect_filled`, and reports typed context/kernel diagnostics. The backend still refuses to mark CUDA usable because the loaded kernels are not yet verified by a passing hardware readback self-test. | Partially complete |
| Host WM and SimpleOS WM share logic | Host and SimpleOS import/use the same WM service/core for create/focus/move/resize/minimize/restore/close/input routing; no local host service shim duplicates WM authority | `host_compositor_entry.spl` imports the real `os.services.wm.wm_service.WmService` for lifecycle state and translates host bridge requests into shared `WmAction` values before applying compositor mutations. Pointer-driven drag/resize also route through `WmAction` lifecycle helpers. Host still has a local `HostCompositor` adapter for host-native surfaces, and `DesktopShell.apply_wm_action` still owns SimpleOS-specific create/destroy/update side effects. | Partially complete |
| Host WM and SimpleOS WM use the same web renderer API | Host and SimpleOS web rendering path both call shared web render API, with tests for the same fixture | `simple_web_window_renderer.spl` builds `WebRenderRequest` values and turns Simple Web pixels into `WebRenderArtifact` values before blitting to `CompositorBackend`. Host compositor renderer-name exposure uses `WEB_RENDER_TARGET_SIMPLE_WEB`. Tests cover artifact dimensions, target identity, and host renderer listing. Host still has host-native surface adapter code outside the common web API. | Partially complete |
| Host WM and SimpleOS WM use the same 2D engine API | Both paths render through `CompositorBackend`/`Engine2D RenderBackend` adapters and do not bypass with direct platform-specific overlay drawing | Compositor/Engine2D adapters exist, but local research found SimpleOS direct Engine2D overlay drawing bypasses compositor surfaces. | Incomplete |
| Pure Simple GUI/web-render path is memory and size optimized against an equivalent Qt GUI app | A measured Simple artifact and a measured equivalent Qt artifact, with the Simple path at or below Qt size and no avoidable allocation regressions in the pure Simple renderer | `src/app/ui.browser/backend.spl` uses pre-sized framebuffer/pixel arrays. `scripts/check-qt-gui-size-baseline.shs` now records the smallest measured Simple Web artifact from `doc/09_report/web_baremetal_size_audit_2026-05-28.md`; current value is 14,336 bytes for `Simple web placeholder URL facade`. Qt development files are missing on this host, so no Qt artifact exists and equal-or-better remains unproven. | Partially complete |
| Research local with agents | Independent local explorer results for web renderer, 2D renderer, WM sharing, and artifact presence | Agents completed and findings were merged into `doc/01_research/local/shared_wm_renderer_unification.md`. | Complete |
| If not complete, plan | Requirement options, NFR options, and staged plan exist | Options and plan are present under `shared_wm_renderer_unification`. | Complete |

## Next Evidence To Produce

1. Architecture and design:
   - `doc/04_architecture/shared_wm_renderer_unification.md`
   - `doc/05_design/shared_wm_renderer_unification.md`
2. System tests:
   - web render API parity spec
   - Engine2D backend interface conformance spec
   - host/SimpleOS WM logic parity spec
3. Implementation evidence:
   - keep shared web render API imported by Web/Electron/Tauri/pure Simple renderer
   - add a CUDA hardware self-test that proves clear and filled-rect readback before marking CUDA 2D usable
   - host WM imports the real `WmService`; remaining work is to route more host-native surface/input behavior through shared WM core paths
   - SimpleOS direct overlay path routed through shared rendering APIs or explicitly out of WM scope
   - Qt toolchain provisioned, or a CI environment that can build the Qt baseline and compare it against the measured Simple Web artifact
