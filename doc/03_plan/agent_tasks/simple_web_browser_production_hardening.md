# Simple Web Browser Production Hardening Agent Plan

## Parallel Agent Split

- Normal model artifact audit: inspect SPipe state, requirements, design, spec docs, reports, and tracking rows for Simple Web/browser hardening lanes. Output canonical lane names and missing artifacts only.
- Spark model implementation reconnaissance: inspect `src/app/ui.web`, `src/app/ui.browser`, browser/Web tests, and evidence wrappers. Output concrete hardening risks and one disjoint implementation slice only.
- Final normal/highest-capability review owns shared interface names, manual `step("...")` helper names, setup/checker helper names, fail-fast placeholders (`assert(false)` or `fail(...)`), generated-manual quality, broad exclusions, and done marks.

## Current Slice

Owns these files:

- `src/app/ui.web/session_token.spl`
- `src/app/ui.web/server.spl`
- `src/app/ui.web/tls_serve_loop.spl`
- `src/app/ui.web/ui_routes.spl`
- `src/app/ui.web/auth_params.spl`
- `test/01_unit/app/ui/web_auth_hardening_spec.spl`
- `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
- `doc/06_spec/03_system/gui/simple_web_browser_production_hardening_spec.md`

Do not absorb unrelated GPU, crypto, compiler, or renderer-parity dirty files in this checkout.

## Latest Evidence

- Live endpoint spec: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 240`
- Unit auth spec: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`
- Unit WebSocket helper spec: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean`
- Auth parser check: `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/server.spl src/app/ui.web/ui_routes.spl test/01_unit/app/ui/web_auth_hardening_spec.spl`

## Remaining Work

- Keep selected Feature Option C and NFR Option C traceability current in final
  requirements, executable specs, generated manuals, and tracking rows.
- Run native Metal evidence on macOS and native ROCm/HIP evidence on an AMD
  ROCm host; the local Linux host can only record host-unavailable verdicts for
  those environments.
