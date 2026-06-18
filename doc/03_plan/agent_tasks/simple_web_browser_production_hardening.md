# Simple Web Browser Production Hardening Agent Plan

## Parallel Agent Split

- Normal model artifact audit: inspect SPipe state, requirements, design, spec docs, reports, and tracking rows for Simple Web/browser hardening lanes. Output canonical lane names and missing artifacts only.
- Spark model implementation reconnaissance: inspect `src/app/ui.web`, `src/app/ui.browser`, browser/Web tests, and evidence wrappers. Output concrete hardening risks and one disjoint implementation slice only.

## Current Slice

Owns these files:

- `src/app/ui.web/session_token.spl`
- `src/app/ui.web/server.spl`
- `src/app/ui.web/tls_serve_loop.spl`
- `src/app/ui.web/ui_routes.spl`
- `src/app/ui.web/auth_params.spl`
- `test/01_unit/app/ui/web_auth_hardening_spec.spl`
- `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
- `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`

Do not absorb unrelated GPU, crypto, compiler, or renderer-parity dirty files in this checkout.

## Latest Evidence

- Live endpoint spec: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 240`
- Unit auth spec: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`
- Unit WebSocket helper spec: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean`
- Auth parser check: `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/server.spl src/app/ui.web/ui_routes.spl test/01_unit/app/ui/web_auth_hardening_spec.spl`

## Last Session Handoff — 2026-06-17

Continue the lane from the current worktree. Do not resume crashed rollout
`019e85dc-fb0c-73b0-b0c6-2a6ead9624ed`.

Completed in the last focused session:

- Resolved focused browser production hardening conflict markers in
  `.spipe/simple_web_browser_production_hardening/state.md`,
  `src/app/ui.web/auth_params.spl`, `src/app/ui.web/server.spl`,
  `src/app/ui.web/async_server.spl`, `src/app/ui.web/tls_serve_loop.spl`,
  `test/01_unit/app/ui/web_auth_hardening_spec.spl`,
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`, and
  `doc/09_report/simple_web_browser_production_hardening.md`.
- Kept the stricter production behavior while resolving conflicts: bounded
  request-head/body framing, sanitized `X-Request-Id`, JSON no-store/no-cache/nosniff
  headers, and HTML anti-sniff/frame-deny/referrer/permissions/CSP headers.
- Updated `scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs`
  with the same headless-safe Electron GPU flags used by the Engine2D evidence
  wrapper.
- Verified `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl src/app/ui.web/async_server.spl
  src/app/ui.web/tls_serve_loop.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`.
- Verified `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple sh
  scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs`; the new
  2026-06-17 Electron layout bitmap report passes with real captured ARGB,
  zero mismatched pixels, and no blur/tolerance.
- Resolved `test/01_unit/app/ui/async_web_spec.spl` conflict markers, keeping
  both JSON no-store/no-cache/nosniff assertions and HTML frame/referrer/CSP assertions.
- Verified `bin/simple check test/01_unit/app/ui/async_web_spec.spl
  src/app/ui.web/async_server.spl src/app/ui.web/auth_params.spl`.
- Verified `bin/simple test test/01_unit/app/ui/async_web_spec.spl
  --mode=interpreter --clean`; the async web unit spec passes with 27
  scenarios.
- Resolved `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
  conflict markers in the executable coverage and traceability tables, keeping
  deprecated query tokens non-authorizing, legacy `/ws` hidden, JSON and HTML
  security-header coverage, and normal/shared-WM/async/TLS request-boundary
  coverage.
- Verified `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple sh
  scripts/check/check-production-gui-web-renderer-parity-evidence.shs`; it wrote
  `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md`
  with top-level status `pass`. Electron matrix, Electron layout manifest,
  Tauri/Chrome surface manifest, and backend parity passed; font offload and
  raw Metal readback remain host/backend-unavailable rows, not parity failures.
- Refreshed `doc/09_report/simple_web_browser_production_hardening.md` to point
  at the 2026-06-17 renderer parity pass and current async web unit pass.
- Refreshed focused generated manuals with `SIMPLE_LIB=src bin/simple
  spipe-docgen test/01_unit/app/ui/async_web_spec.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index`; later focused live-endpoint docgen now reports
  `OK simple_web_browser_production_hardening_spec (125 lines)`.
- Ran the doc layout guard: `find doc/06_spec -name '*_spec.spl' | wc -l`
  returned `0`.
- Added the expected top-level architecture pipeline artifact
  `doc/04_architecture/simple_web_browser_production_hardening.md`, pointing to
  the detailed UI architecture note, and added the missing detail design
  artifact `doc/05_design/simple_web_browser_production_hardening.md`.
- Focused artifact audit now confirms required requirements, architecture,
  design, system-test plan, executable specs, generated manuals, and renderer
  reports are present.
- Updated `doc/08_tracking/feature/feature_db.sdn` row
  `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16` to include the canonical
  architecture/design artifacts, async unit/generated spec evidence, and
  2026-06-17 evidence dates while keeping status `current`.
- Verified `bin/simple lint doc/08_tracking/feature/feature_db.sdn`.

Additional focused local hardening completed after that handoff:

- Added `ui_web_script_security_headers` and applied no-store/no-cache/nosniff guards to
  normal-server `/wm.js` and `/retained_renderer.js` responses, plus existing
  JSON no-store/no-cache/nosniff guards to successful `/api/state` and
  `/api/widgets` responses.
- Added unit coverage for the script header helper in
  `test/01_unit/app/ui/web_auth_hardening_spec.spl`; the focused auth
  hardening spec passed with 21 scenarios.
- Added live normal-server assertions for `/wm.js` and `/retained_renderer.js`
  no-store/no-cache/nosniff headers in
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; the
  focused live endpoint spec passed with 6 scenarios.
- Added live normal and shared-WM assertions for `/wm/native_window` HTML
  security headers and unknown-route JSON `404 not_found` fallback
  no-store/no-cache/nosniff headers in
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; the
  focused live endpoint spec passed with 6 scenarios.
- Added live authenticated `/api/state` and `/api/widgets` success-path
  assertions for `200 OK` plus no-store/no-cache/nosniff headers in
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; the
  focused live endpoint spec passed with 6 scenarios.
- Regenerated `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  and confirmed `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.
- Refreshed `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`,
  `doc/09_report/simple_web_browser_production_hardening.md`, and
  `doc/08_tracking/feature/feature_db.sdn` so JSON/static-script header
  traceability names both `/wm.js` and `/retained_renderer.js`.
- Verified `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` and
  `bin/simple lint doc/08_tracking/feature/feature_db.sdn`.

Current known focused gaps:

- `doc/09_report/electron_simple_web_layout_bitmap_evidence_2026-06-16.md`
  remains a historical failing report. Prefer the 2026-06-17 passing report for
  current evidence; do not delete older evidence unless explicitly asked.
- External host proof remains open for macOS Metal, AMD ROCm/HIP, Windows
  DirectX, and real browser WebGPU device readback.
- Use `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`
  for the exact commands and acceptance fields for those host gates.

Fresh-session plan for work after rollout 019e85dc-fb0c-73b0-b0c6-2a6ead9624ed:

Scope this lane to the browser production hardening follow-up only. Preserve all
unrelated dirty files from the concurrent Electron, GPU database offload,
compiler/runtime, office, and proxy lanes.

Current local status:

- Local browser hardening evidence is WARN, not PASS, because all local checks
  passed but external rendering gates remain open.
- The latest focused sessions added static script/API cache and sniffing
  headers, live `/wm.js`, `/retained_renderer.js`, `/wm/native_window`, and
  unknown-route fallback assertions, refreshed the generated/manual specs,
  updated traceability docs, and recorded local completion evidence in
  `doc/09_report/simple_web_browser_local_completion_audit_2026-06-17.md`.
- Focused compile evidence is recorded for
  `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl test/03_system/gui/simple_web_browser_production_hardening_spec.spl`.
- Do not rerun already-green focused browser tests unless a new edit invalidates
  their evidence.

Next ordered work:

1. Do not rerun the 2026-06-17 green renderer parity, Electron layout bitmap,
   async unit, docgen, or `doc/06_spec` layout checks unless a focused source or
   spec change invalidates them.
2. Use `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`
   as the current audit artifact for the remaining release gate. The only open
   focused gap is external proof on hosts this Linux checkout cannot emulate:
   macOS Metal native readback, AMD ROCm/HIP native readback, Windows DirectX
   native readback, and real browser WebGPU `device_readback`.
3. Continue external proof through the blocked follow-up feature
   `SIMPLE_WEB_BROWSER_EXTERNAL_NATIVE_READBACK_PROOF_2026_06_17` and plan
   `doc/03_plan/agent_tasks/simple_web_browser_external_native_readback_proof.md`;
   use `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
   for any completed host proof.
4. Before commit or release only, refresh workspace hygiene evidence and run one
   final focused verification matrix once: focused `bin/simple check`,
   focused unit/system specs, renderer parity report status check, feature DB
   lint, and doc layout guard.

## Fresh Session Plan — 2026-06-17

Scope for a fresh non-resume session after crashed rollout
`019e85dc-fb0c-73b0-b0c6-2a6ead9624ed`:

- Preserve unrelated dirty files. The current lane owns the Simple Web browser
  hardening docs, specs, reports, selected `src/app/ui.web` hardening files, and
  the Electron layout evidence wrapper only. The external host evidence manifest
  template at
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
  is part of this lane's proof handoff.
- Treat `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`
  as the active audit artifact. It is the bridge between the last successful
  local evidence and the remaining external host gates.
- Current local result: latest focused sessions produced passing 2026-06-17
  Electron layout bitmap and production renderer parity reports, passing async
  web unit evidence, a clean 125-line live endpoint manual, and live
  authenticated `/api/state` and `/api/widgets` success-header evidence plus
  normal/shared-WM evidence for `/wm.js`, `/retained_renderer.js`,
  `/wm/native_window`, and unknown-route fallback headers.
- Current blocker: this Linux host cannot complete macOS Metal, AMD ROCm/HIP,
  Windows DirectX, or real browser WebGPU device-readback proof.
- Tracked external follow-up:
  `SIMPLE_WEB_BROWSER_EXTERNAL_NATIVE_READBACK_PROOF_2026_06_17` /
  `doc/03_plan/agent_tasks/simple_web_browser_external_native_readback_proof.md`.
- Current-host blocker report:
  `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md`.
- Stop condition for the next focused turn: complete one external proof artifact
  using `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
  under the tracked external follow-up, or report the host blocker after one
  relevant focused command.

## Remaining Work

- Keep selected Feature Option C and NFR Option C traceability current in final
  requirements, executable specs, generated manuals, and tracking rows.
- Run native Metal evidence on macOS and native ROCm/HIP evidence on an AMD
  ROCm host; the local Linux host can only record host-unavailable verdicts for
  those environments.
