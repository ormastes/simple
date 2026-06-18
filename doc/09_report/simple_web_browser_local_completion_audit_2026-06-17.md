# Simple Web Browser Local Completion Audit - 2026-06-17

## Scope

This audit covers the selected Simple Web browser production hardening Feature
Option C and NFR Option C requirements on the current Linux host. It does not
claim release completion for external native rendering gates.

## Local Result

STATUS: WARN

- PASS: `REQ-WEB-HARD-001` through `REQ-WEB-HARD-013` trace to current source,
  executable specs, generated manuals, and/or renderer parity evidence in
  `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`.
- WARN: `REQ-WEB-HARD-014` remains partial because native macOS Metal, AMD
  ROCm/HIP, Windows DirectX, and real browser WebGPU device-readback proof
  require external hosts.
- PASS: `NFR-WEB-HARD-001` through `NFR-WEB-HARD-011` trace to current source,
  executable specs, generated manuals, and report evidence.
- WARN: `NFR-WEB-HARD-012` remains partial for the same external
  device-readback gates.

## Current Local Evidence

- Focused stub scan over `src/app/ui.web/auth_params.spl`,
  `src/app/ui.web/server.spl`,
  `test/01_unit/app/ui/web_auth_hardening_spec.spl`, and
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` is
  clean for `pass_todo`, placeholder `pass_do_nothing`, `todo(`, `TODO`,
  `FIXME`, placeholder assertions, and unsupported-operation markers.
- `src/app/ui.web/server.spl` now propagates the fallback UI parse error instead
  of silently ignoring it; `bin/simple check src/app/ui.web/server.spl` passed.
- After the fallback parse error handling change and subsequent browser response
  header hardening, `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios, including
  authenticated `/api/state` and `/api/widgets` `200 OK` plus
  no-store/no-cache/nosniff assertions.
- Post-change focused compile check passed for `src/app/ui.web/auth_params.spl`,
  `src/app/ui.web/server.spl`,
  `test/01_unit/app/ui/web_auth_hardening_spec.spl`, and
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`.
- `sh scripts/audit/numbered-artifact-guard.shs --working` returned
  `Numbered artifact guard: OK`.
- `sh scripts/audit/numbered-artifact-guard.shs --staged` returned
  `Numbered artifact guard: OK`.
- Focused SPipe-quality scan over
  `test/01_unit/app/ui/web_auth_hardening_spec.spl` and
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` returned
  no matches for `pass_todo`, placeholder `expect(true).to_equal(true)`,
  deprecated truthy helpers, placeholder no-ops, TODO/FIXME, or `todo(`.
- `test/01_unit/app/ui/web_auth_hardening_spec.spl` covers secret policy,
  origin/bearer parsing, request bounds, sanitized request IDs, fixed-window
  login behavior, JSON headers, and static script header helpers.
- `test/01_unit/app/ui/async_web_spec.spl` covers async JSON and HTML response
  security-header behavior.
- `test/01_unit/app/ui/ws_handler_spec.spl` covers canonical WebSocket bearer
  transport and query-token non-authorization.
- `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` covers
  live fail-closed HTTP/WebSocket behavior, canonical `/ui/ws`, hidden legacy
  `/ws`, authenticated `/api/state` and `/api/widgets` success headers, live
  JSON/HTML/static-script headers, warm auth latency, request bounds, and process
  cleanup.
- `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  includes authenticated `/api/state` and `/api/widgets` success-header
  assertions plus live `/wm.js`, `/retained_renderer.js`, `/wm/native_window`,
  and hidden-route fallback header assertions.
- `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md`
  records the local production renderer parity pass.
- `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md`
  records why this Linux host cannot close the external native proof gates.

## Remaining Release Blocker

Run the commands in
`doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md` on the
required macOS Metal, AMD ROCm/HIP, Windows DirectX, and WebGPU-capable browser
hosts, and capture each result with
`doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`.
Only accepted native device-readback evidence should move the feature DB row
from `current` to `done`.
