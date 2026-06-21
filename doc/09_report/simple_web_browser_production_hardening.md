# Simple Web Browser Production Hardening Report

## Current Evidence

- Auth/parser check: focused `bin/simple check` passed for `server.spl`,
  `tls_serve_loop.spl`, `async_server.spl`,
  `simple_web_browser_production_hardening_spec.spl`,
  `web_auth_hardening_spec.spl`, and `ws_handler_spec.spl`.
- Unit auth spec: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passed with 21 scenarios on 2026-06-17 after adding request-head boundary and static script-header coverage.
- Static script/API header check: `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl` passed on 2026-06-17 after adding no-store/no-cache/nosniff guards to normal-server JavaScript responses and successful JSON state/widget responses.
- Focused source/spec compile check: `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passed after the static script/API header hardening and live `/wm.js` assertions.
- Generated auth hardening manual:
  `doc/06_spec/test/01_unit/app/ui/web_auth_hardening_spec.md` is newer than
  `test/01_unit/app/ui/web_auth_hardening_spec.spl` and includes the browser
  script-header scenario.
- Unit async web spec: `bin/simple test test/01_unit/app/ui/async_web_spec.spl --mode=interpreter --clean` passed with 27 scenarios.
- Unit WebSocket helper spec: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` passed with 12 scenarios.
- Live endpoint spec: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360` passed with 6 scenarios on 2026-06-17 after adding authenticated `/api/state` and `/api/widgets` `200 OK` no-store/no-cache/nosniff assertions plus live normal-server and shared-WM `/wm.js`, `/retained_renderer.js`, `/wm/native_window`, and unknown-route fallback header assertions.
- Generated live endpoint manual:
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  was regenerated with `SIMPLE_LIB=src bin/simple spipe-docgen
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index` and includes authenticated `/api/state` and
  `/api/widgets` success-header assertions plus normal-server and shared-WM
  `/wm.js`, `/retained_renderer.js`, `/wm/native_window`, and
  `/hidden-browser-production-gap` fallback assertions; docgen now reports
  `OK simple_web_browser_production_hardening_spec (125 lines)`.
- Traceability refresh: `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
  and the `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16` feature DB row
  now include JSON/static-script response header hardening evidence for
  `/wm.js` and `/retained_renderer.js`; `bin/simple lint
  doc/08_tracking/feature/feature_db.sdn` passed.
- Local completion audit:
  `doc/09_report/simple_web_browser_local_completion_audit_2026-06-17.md`
  records local PASS coverage for `REQ-WEB-HARD-001` through
  `REQ-WEB-HARD-013` and `NFR-WEB-HARD-001` through `NFR-WEB-HARD-011`, with
  WARN status for the external `REQ-WEB-HARD-014` / `NFR-WEB-HARD-012`
  device-readback gates.
- Focused stub audit: removed a placeholder-looking fallback UI parse no-op in
  `src/app/ui.web/server.spl`, verified `bin/simple check
  src/app/ui.web/server.spl`, and reran the focused stub scan with no matches.
- Post-server-change live endpoint verification: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios.
- Post-change focused compile check: `bin/simple check
  src/app/ui.web/auth_params.spl src/app/ui.web/server.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passed.
- Numbered artifact guard: `sh scripts/audit/numbered-artifact-guard.shs
  --working` returned `Numbered artifact guard: OK`.
- Staged numbered artifact guard: `sh scripts/audit/numbered-artifact-guard.shs
  --staged` returned `Numbered artifact guard: OK`.
- Focused SPipe-quality scan over the auth hardening and live endpoint specs
  returned no placeholder assertions, deprecated truthy helpers, no-op
  placeholders, TODO/FIXME markers, or `pass_todo`.
- Spec docgen: `SIMPLE_LIB=src bin/simple spipe-docgen test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output doc/06_spec --no-index` reports
  `OK simple_web_browser_production_hardening_spec (125 lines)` and regenerated
  the 6-scenario manual with `/wm/native_window` and hidden-route fallback evidence.
- Production renderer parity: `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs` passed on 2026-06-17 and wrote `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md`.
- Layout guard: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`
  after the focused auth and live endpoint manual refresh checks.

## Implemented Hardening

- Production token secrets fail closed unless explicitly opted into local
  non-TLS dev fallback.
- TLS mode never uses the insecure dev secret.
- Login origin checks fail closed before token minting.
- `/ui/ws`, `/ui/resume`, and sensitive `/api/*` require origin-bound bearer
  authorization, including `/api/state`, `/api/widgets`, and the async
  `/api/clients` route.
- Legacy `/ws` and arbitrary WebSocket upgrade paths are hidden with
  `404 Not Found` before authorization or upgrade handling.
- Browser JSON response helpers across normal, async, TLS, and shared `/ui/*`
  paths set `Cache-Control: no-store`, `Pragma: no-cache`, and
  `X-Content-Type-Options: nosniff`.
- Normal and shared-WM unknown browser routes now use the centralized JSON
  `404 not_found` fallback, and the live endpoint spec proves
  `/hidden-browser-production-gap` inherits `Cache-Control: no-store`,
  `Pragma: no-cache`, and `X-Content-Type-Options: nosniff`.
- Normal-server successful `/api/state` and `/api/widgets` JSON responses now
  use the same no-store/no-cache/nosniff guards as error and auth JSON
  responses, with live success-path assertions for both routes.
- Browser static script responses for `/wm.js` and `/retained_renderer.js`
  now use no-store/no-cache/nosniff guards in both direct normal-server handling and
  shared `_simple_response` handling.
- The live normal-server scenario now requests `/wm.js` and
  `/retained_renderer.js`, then verifies
  `Cache-Control: no-store`, `Pragma: no-cache`, and
  `X-Content-Type-Options: nosniff` on the actual HTTP responses.
- Async/TLS/static response inspection on 2026-06-17 found no separate async or
  TLS JavaScript-serving path requiring the script-header patch; shared-WM
  `/wm.js` is covered by `_simple_response`.
- Browser HTML document response helpers across normal, async, and TLS paths
  set `X-Content-Type-Options: nosniff`, `X-Frame-Options: DENY`,
  `Referrer-Policy: no-referrer`, `Permissions-Policy`, and a restrictive
  `Content-Security-Policy`; the live endpoint spec covers the normal root page
  and the shown `/wm/native_window` HTML surface in both normal and shared-WM
  server paths.
- Login and resume JSON responses echo only sanitized `X-Request-Id` values,
  rejecting bearer-like or otherwise unsafe correlation strings.
- Authorized `/ui/resume` rejects missing or malformed `session_id`,
  `snapshot_revision`, or `last_sequence` with `400 Bad Request`, and accepts
  strict valid body fields in the normal TCP server path.
- Authorized `/ui/resume` rejects oversized JSON bodies with `413 Payload Too
  Large` before parsing route fields.
- Browser POST body readers across normal, shared-WM, async, and TLS paths
  reject malformed or ambiguous request framing with `400 Bad Request`,
  including duplicate `Content-Length` and unsupported `Transfer-Encoding`,
  before reading body bytes.
- Inbound WebSocket frame readers reject declared payload lengths above the
  production cap before allocating payload buffers.
- The normal, shared-WM, async, and TLS HTTP entrypoints reject oversized
  request heads, request lines, and header lines before route dispatch.
- `/ui/ws`, async, and TLS WebSocket upgrade paths reject non-GET upgrade
  attempts with `405 Method Not Allowed` before the socket can be upgraded,
  even when the request carries a valid origin-bound bearer token.
- WebSocket upgrade detection and key extraction honor case-insensitive HTTP
  header names and require a `Connection` token of `Upgrade`; live endpoint
  evidence covers lowercase/mixed-case successful upgrade headers.
- Generated browser clients and static `wm.js` use WebSocket subprotocol bearer
  tokens instead of query-string tokens.
- Query-string bearer compatibility is non-authorizing in production; the
  deprecated `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` flag no longer enables token
  redemption.
- `/ui/login` is bounded by a fixed-window burst gate in both normal and shared
  WM server paths.
- Warm production browser authentication latency is measured by the live
  endpoint spec for a warmed token mint plus authenticated WebSocket upgrade
  path with a 10s local ceiling.
- The shared-WM web server parses `SIMPLE_UI_WEB_PORT` as a concrete integer,
  so `SIMPLE_UI_WEB_SHARED_WM=1` starts on the requested port and its login
  burst gate has live socket evidence.
- The normal `run_web` accept loop preserves per-server state across
  connections, so the login burst gate is enforced across repeated TCP
  requests.
- Production renderer parity wrapper now passes locally with top-level status
  `pass`: Electron matrix, Electron CSS/layout manifest, Tauri/Chrome surface
  manifest, CPU SIMD parity, and the Metal-path parity contract. This local
  Linux report is not native Metal device-readback proof; native Metal remains
  covered by the external host evidence runbook. The layout/surface manifests
  cover 18 cases with 16 exact passes, 2 tracked text-raster divergence rows,
  and 0 failures; blur/tolerance remains unused.

## Host Environment Evidence

- Linux NVIDIA Vulkan/CUDA/OpenCL evidence exists in
  `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`; the
  refreshed 2026-06-16 host-GPU wrapper reports same-frame
  Vulkan/BrowserBackend device readback and Linux GUI/web queue integration
  `pass`.
- macOS Metal is host-unavailable locally and must be proven on macOS.
- AMD ROCm/HIP is host-unavailable locally and must be proven on an AMD ROCm
  host.
- Windows DirectX native proof is host-unavailable locally and must be proven
  on a Windows/DirectX host.
- Browser WebGPU real-device readback is not proven locally; current evidence
  is matrix/provenance only and must be replaced by native device-readback
  evidence on a WebGPU-capable browser host.
- External-host commands and field-level acceptance criteria are recorded in
  `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`.
- Fillable external-host evidence manifests should use
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
  before any remaining native rendering gate is marked closed.
- The environment-bound follow-up is tracked separately as
  `SIMPLE_WEB_BROWSER_EXTERNAL_NATIVE_READBACK_PROOF_2026_06_17` with plan
  `doc/03_plan/agent_tasks/simple_web_browser_external_native_readback_proof.md`
  and feature request
  `doc/08_tracking/feature/simple_web_browser_external_native_readback_proof_2026-06-17.md`.
- Current-host blocker evidence from 2026-06-17 is recorded in
  `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md`; this
  host is Linux and lacks the required Metal, ROCm/HIP, Windows DirectX, and
  real WebGPU device-readback proof environment.

## Workspace Hygiene Evidence

Snapshot from 2026-06-17:

- The working copy still contains unrelated dirty files outside this lane.
  Representative unrelated paths include `.spipe/ide_md_counter_office_hardening/state.md`,
  `.spipe/simple_web_browser_production_hardening/state.md` sibling state
  changes from this lane, GPU/web DB offload docs and specs, compiler/runtime
  GPU changes, and untracked example roots.
- `jj --no-pager log -r 'conflicts()'` reports 498 existing conflict commits.
  Representative unrelated conflict rows include `wyruwlsklnzt 3af695013cf1
  docs(compute): add std.compute/ExecTarget guide+tldr; spipe skill testing
  patterns`, `yoqtkuwktyqr 21828c2b7e72 feat(compute): per-backend
  compute-kernel emission (cuda/hip/opencl/metal/webgpu)`, and
  `tmsqprwsruws ba42e2fc8a50 fix(ui.web): share auth query parsing`.
- These files and conflicts are not part of the browser-hardening commit scope.

## Remaining Release Work

- Selected Feature Option C and NFR Option C are recorded in final requirement
  files, and trace IDs are carried by the executable specs, generated manuals,
  and system test plan.
- Live async-server request-head evidence is blocked by an existing
  `rt_sqlite_open` extern failure in the async server interpreter launch path;
  the parser guard itself is covered by shared unit predicates and compile
  checks for `async_server.spl` and `tls_serve_loop.spl`.
- `doc/03_plan/sys_test/simple_web_browser_production_hardening.md` contains
  the current traceability matrix from every selected `REQ-WEB-HARD-*` and
  `NFR-WEB-HARD-*` ID to evidence artifacts.
- AC-7 hygiene evidence must remain separately reported until unrelated dirty
  files and existing `jj` conflicts are resolved outside this lane.
- `doc/08_tracking/feature/feature_db.sdn` has a `current` row for this lane;
  do not mark it `done` until macOS Metal/AMD ROCm/DirectX/WebGPU host
  evidence is complete.
