# Web/Tauri Parity Parallel Lane - 2026-05-29

Scope owned by this lane:
- `src/lib/common/ui/web_render_api.spl`
- `src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
- `src/app/ui.browser/renderer.spl`
- `test/01_unit/app/ui/web_render_backend_api_spec.spl`

Inspection:
- Tauri and Electron already render through `WebRenderRequest` and `web_render_to_artifact`.
- Pure Simple browser frame rendering now enters through `web_render_url_to_request` and `web_render_url_request_to_pixels`.
- The remaining scoped diff was that `web_render_default_page_html` in the pixel backend still delegated to the low-level Simple Web default page helper instead of the common request/full-HTML envelope.

Change:
- Kept the existing pixel-backend helper signature stable.
- Routed pixel-backend default page HTML through `web_render_url_request` plus `web_render_full_html` with `WEB_RENDER_TARGET_PURE_SIMPLE`.
- Added focused SPipe coverage that the pixel facade URL request matches the common URL request body and that default page HTML uses the shared `<div id="app">` envelope shape.

Commands and results:
- `bin/simple test test/01_unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter`
  - Initial scoped baseline before final patch: PASS, 7 tests, 2268 ms.
- `bin/simple test test/01_unit/app/ui/web_render_backend_api_spec.spl --mode=interpreter`
  - Final result: PASS, 7 tests, 3183 ms.
- `bin/simple check src/lib/common/ui/web_render_api.spl`
  - PASS.
- `bin/simple check src/lib/gc_async_mut/ui/web_render_pixel_backend.spl`
  - PASS.
- `bin/simple check src/app/ui.browser/renderer.spl`
  - PASS.

Remaining blockers:
- None in this scoped lane.
