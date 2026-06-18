# Feature: simple-web-browser-production-hardening

## Raw Request

`$sp_dev harden simple web browser in production level. do with multiple agents with normal and spark llm in pherallel after deep plan`

## Task Type

feature

## Refined Goal

Harden the Simple Web/browser production boundary so renderer parity, browser bridge evidence, and web UI runtime authentication fail closed under production settings while retaining explicit opt-in local development behavior.

## Acceptance Criteria

1. Production token signing secrets must come from `SIMPLE_UI_WEB_TOKEN_SECRET`; missing secrets must fail startup unless a non-TLS local developer explicitly sets `SIMPLE_UI_WEB_ALLOW_INSECURE_DEV_SECRET=1`.
2. TLS web serving must never use the insecure non-TLS secret fallback path.
3. `/ui/login` must fail closed when the HTTP `Origin` header is missing or disallowed; it must not mint tokens for `unknown` origins.
4. `/ui/ws` and `/ui/resume` must require both an allowed origin and a valid bearer token bound to that origin.
5. Production renderer/browser evidence gates remain marker-free and exact for the existing GUI/Web renderer parity slice.
6. Browser/Web hardening tests must include real assertions and must not use `pass_todo`, empty bodies, or boolean-wrapper placeholder passes.
7. Verification must report unrelated dirty files and the existing `jj` conflict separately from this lane.

## Deep Plan

1. Artifact audit: identify existing renderer parity and browser WASM/WebGPU lanes, then create the missing production-browser hardening state so new auth/runtime work has its own scope.
2. Parallel reconnaissance: use one normal model for SPipe artifact gaps and one Spark model for implementation/test risk discovery.
3. Security boundary slice: harden token secret policy, TLS secret wiring, login origin behavior, and resume route auth without touching renderer/GPU files.
4. Evidence slice: add focused unit specs for the security policy and origin fail-closed behavior.
5. Verification: run focused checks/tests for new files and note pre-existing broad-check blockers separately.
6. Follow-up production slices: keep selected Feature Option C/NFR Option C traceability current, and run native host evidence for macOS Metal plus AMD ROCm/HIP.

## Phase

verification / external-host evidence pending

## Log

- dev: Created production browser-hardening state after parallel normal/Spark agent reconnaissance.
- impl: Added first security-boundary slice for fail-closed token secret policy, TLS secret mode, `/ui/login` origin handling, and `/ui/resume` bearer/origin auth.
- impl: Added explicit exports for `TOKEN_TTL_DEFAULT_MS` and TLS SFFI symbols so the hardened web server/TLS modules check cleanly through their current imports.
- impl: Added shared `ui_web_authorization_status` / `ui_web_request_authorized` policy and gated `/api/state`, `/api/widgets`, and `/api/clients` style sensitive JSON endpoints across plain, TLS, and async web loops.
- impl: Migrated generated legacy and WM browser JavaScript to authenticate through `/ui/login` before opening WebSockets, and required origin-bound bearer tokens on legacy `/ws` and async WebSocket upgrade paths.
- impl: Made `AsyncWebServer` fail startup on missing production token secrets unless explicit non-TLS insecure-dev opt-in is set, matching the plain and TLS server policy.
- impl: Added one-pass percent decoding for query bearer tokens in both modern route authorization and legacy WebSocket extraction so browser `encodeURIComponent(token)` output verifies as the original signed token.
- impl: Hardened default OriginGuard semantics so built-in local development policy accepts only loopback HTTP/HTTPS origins with optional numeric ports, while explicit `SIMPLE_UI_WEB_ALLOWED_ORIGINS` allowlists remain exact.
- impl: Added pure `OriginGuard.from_env_value` parsing coverage for trimmed exact explicit allowlists so the default loopback development policy stays separate from configured production origins.
- verify: `bin/simple check src/app/ui.web/ui_routes.spl src/app/ui.web/server.spl src/app/ui.web/tls_serve_loop.spl src/app/ui.web/async_server.spl src/app/ui.web/session_token.spl src/lib/nogc_sync_mut/io/tls_sffi.spl test/01_unit/app/ui/web_auth_hardening_spec.spl` passes.
- verify: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter` passes with 7 scenarios. The positive HMAC token path remains covered by production code but is not asserted in this interpreter unit spec because `rt_hmac_sha256` is unavailable in that runner lane.
- verify: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter` passes with 7 scenarios, including decoded query bearer extraction from non-leading query positions.
- verify: `bin/simple check src/app/ui.web/origin_guard.spl test/01_unit/app/ui/web_auth_hardening_spec.spl` passes.
- verify: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter` passes with 8 scenarios after explicit allowlist parser coverage.
- impl: Added live system-level raw HTTP/WebSocket endpoint evidence in `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`, using the test-only launcher `test/03_system/gui/ui_browser/simple_web_hardening_server.spl` to call production `app.ui.web.server.run_web` directly while avoiding the current unstable `simple ui` command dispatcher.
- verify: `bin/simple check test/03_system/gui/simple_web_browser_production_hardening_spec.spl test/03_system/gui/ui_browser/simple_web_hardening_server.spl` passes.
- verify: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 90` passes with 1 live endpoint scenario covering missing-origin `/ui/login`, oversized unauthenticated `/ui/login`, unauthenticated `/api/state`, and unauthenticated `/ui/ws`.
- verify: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passes with 8 scenarios.
- verify: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` passes with 9 scenarios.
- impl: Moved login and resume auth-path JSON body field extraction to bounded shared `ui_web_auth_json_field` in `src/app/ui.web/auth_params.spl`, replacing duplicate ad hoc auth parsers in `server.spl` and `ui_routes.spl`.
- verify: `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/server.spl src/app/ui.web/ui_routes.spl test/01_unit/app/ui/web_auth_hardening_spec.spl` passes.
- verify: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passes with 9 scenarios after bounded auth JSON parser coverage.
- verify: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` passes with 9 scenarios.
- verify: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 90` passes with 1 live endpoint scenario after the shared parser refactor.
- plan: Added `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` for local NVIDIA Vulkan/CUDA/OpenCL, Linux Vulkan CPU emulation, macOS Metal, Linux AMD ROCm/HIP, and QEMU/emulation lanes.
- verify: Local GPU environment probes show Vulkan Engine2D readback `pass`; Metal generated readback host-unavailable with `missing-primary-tool`; ROCm generated readback host-unavailable with `missing-primary-tool`.
- verify: Aggregate host GPU queue wrapper reports Vulkan/CUDA/OpenCL readback `pass`, Metal/ROCm host-unavailable, and aggregate queue integration `fail` due `browser-frame-first-render-budget-not-met`.
- impl: Rewrote UI route auth gates and WM login origin handling to avoid early `return` inside value-producing `match` expressions on fail-closed paths.
- impl: Added explicit `/ui/resume` and `/ui/ws` authorization coverage proving missing bearer, disallowed origin, malformed token, and valid origin-bound bearer outcomes.
- verify: `bin/simple check src/app/ui.web/ui_routes.spl src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl` passes.
- verify: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passes with 12 scenarios.
- verify: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` passes with 9 scenarios.
- verify: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 180` passes with 2 live endpoint scenarios.
- impl: Hardened `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` after local verification exposed a flaky 20s Chrome live-capture budget and a font-offload status variable collision.
- verify: `sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs` passes. Evidence reports matrix/layout/surface/backend `pass`, Tauri and Chrome surface fail counts `0`, two tracked text raster divergences per surface, font offload `unavailable`, and Metal readback `unavailable` on Linux with `metal-requires-macos`.
- impl: Disabled query-string bearer token extraction by default behind `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1` and migrated the static `src/app/ui.web/wm.js` production client to WebSocket subprotocol bearer auth.
- impl: Added fixed-window `/ui/login` burst gating to both normal and shared WM server login paths.
- design: Added implementation-aligned architecture, detail design, system-test plan, and report artifacts for the production hardening lane; at that point final `REQ-*`/`NFR-*` documents had not yet been selected.
- verify: `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/ui_routes.spl src/app/ui.web/server.spl src/app/ui.web/ws_handler.spl test/01_unit/app/ui/ws_handler_spec.spl test/01_unit/app/ui/web_auth_hardening_spec.spl` passes.
- verify: Previously, `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passed with 13 scenarios before authorized resume body-contract coverage was added.
- verify: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` passes with 10 scenarios.
- verify: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 180` passes with 2 live endpoint scenarios after query-token fallback was disabled by default.
- verify: `bin/simple spipe-docgen test/01_unit/app/ui/ws_handler_spec.spl test/01_unit/app/ui/web_auth_hardening_spec.spl --output doc/06_spec` completes with existing docgen warnings and stub-style manuals.
- verify: `find doc/06_spec -name '*_spec.spl' | wc -l` returns `0`.
- docs: Added a `current` feature tracking row and refreshed UI guide links for
  the canonical production renderer parity and live web endpoint hardening
  gates. The lane was not `done` because final feature/NFR option selection,
  trace-ID backfill, and native macOS Metal / AMD ROCm host evidence were still
  open.
- fix: Kept `WebServer.serve_loop` on the live instance instead of routing each
  accepted connection through a value-copy helper, so normal `run_web`
  preserves login burst counters across TCP requests.
- fix: Added `429 Too Many Requests` status text in plain, TLS, and async web
  response helpers.
- verify: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 240` passes with 3 live endpoint scenarios covering fail-closed `/ui/login`, `/api/state`, `/api/widgets`, bare `/ui/ws`, query-token `/ui/ws`, positive subprotocol bearer upgrade, and live login burst rate limiting.
- impl: Added normal `run_web` fail-closed handling for unauthenticated
  `/ui/resume` before the unsupported path can fall through to 404.
- verify: Superseded 4-scenario live endpoint coverage added `/ui/resume`,
  legacy `/ws`, and query-token compatibility evidence before the shared-WM
  login burst scenario and later production route-hiding/query-token
  non-authorization changes replaced that compatibility behavior.
- fix: Parsed `SIMPLE_UI_WEB_PORT` as a concrete integer in shared-WM web mode
  instead of formatting the optional parse result into the socket address.
- verify: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360` passes with 5 live endpoint scenarios, adding shared-WM login burst rate-limit evidence to the normal `run_web` endpoint coverage.
- plan: Refined `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` with fresh local Vulkan/Metal/ROCm/WebGPU evidence fields plus explicit Windows DirectX native and browser WebGPU real-device readback plans. Local Vulkan remains `pass`; Metal/ROCm/WebGPU remain host-unavailable/not-device-readback on this Linux host.
- requirements: Made feature and NFR option docs selection-ready by adding
  cumulative candidate `REQ-WEB-HARD-*` and `NFR-WEB-HARD-*` IDs plus final-file
  instructions, without selecting an option or writing final requirement files.
- fix: Hardened authorized `/ui/resume` handling so missing or malformed
  `session_id`, `snapshot_revision`, or `last_sequence` fields return `400`
  instead of defaulting to zero-like values, and normalized normal/shared-WM TCP
  resume responses without relying on interpreter-unsafe `ConnStream` downcasts.
- verify: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passes with 14 scenarios, and `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360` passes with 5 live endpoint scenarios including malformed and valid authorized `/ui/resume`.
- fix: Rejected non-GET WebSocket upgrade attempts for `/ui/ws` and legacy
  `/ws` with `405 Method Not Allowed` before either normal or shared-WM paths
  can upgrade the socket.
- verify: `bin/simple check src/app/ui.web/server.spl src/app/ui.web/ui_routes.spl test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passes, and `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360` passes with 5 live endpoint scenarios including valid-token POST upgrade rejection.
- verify: `bin/simple spipe-docgen test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output doc/06_spec` regenerated the system manual with existing docgen warnings/stub classification.
- verify: AC-7 hygiene snapshot recorded in `doc/09_report/simple_web_browser_production_hardening.md`: unrelated working copy has 107 tracked changes and 5 untracked example roots, while `jj log -r 'conflicts()'` reports 498 existing conflict commits outside this lane.
- docs: Added an initial pre-selection traceability matrix in
  `doc/03_plan/sys_test/simple_web_browser_production_hardening.md` mapping
  every candidate `REQ-WEB-HARD-*` and `NFR-WEB-HARD-*` ID to current evidence
  while preserving final option selection as a then-current release blocker.
- verify: Added warm production browser auth latency evidence to
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; the
  live endpoint spec passes with 6 scenarios and measures warmed token mint plus
  authenticated WebSocket upgrade under a 10s local ceiling.
- fix: Hardened WebSocket upgrade parsing so header names are case-insensitive,
  `Connection` must contain an `Upgrade` token, and `Sec-WebSocket-Key`
  extraction accepts lowercase/mixed-case clients.
- verify: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean`
  passes with 10 scenarios, and the live endpoint spec covers a lowercase
  authenticated `/ui/ws` upgrade path.
- docs: Aligned GPU/browser release blockers across architecture, plan, and
  report so Metal, AMD ROCm, DirectX, and browser WebGPU native proof all remain
  explicit external-host evidence requirements.
- verify: Extended sensitive API auth policy unit coverage to name
  `/api/widgets` and async `/api/clients` alongside `/api/state`.
- docs: Aligned `doc/07_guide/app/ui/ui_render.md` with the current live
  browser-hardening command timeout of `--timeout 360`.
- verify: Added live coverage that token-bearing `/ui/login` JSON responses set
  no-store/no-cache and anti-sniff headers.
- fix: Added explicit oversized-body classification for authorized
  `/ui/resume`, returning `413 Payload Too Large` before route-field parsing in
  normal, shared-WM, and shared `/ui/*` route handlers.
- verify: `bin/simple check src/app/ui.web/server.spl src/app/ui.web/ui_routes.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl
  --mode=interpreter --clean`, and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- fix: Routed async and TLS request-head parsing through the shared
  `ui_web_request_head_status` helper so request-line, header-line, and total
  head limits match normal and shared-WM server behavior. TLS `ConnStream`
  line buffering also fails closed if buffered data exceeds the shared head cap.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/auth_params.spl src/app/ui.web/async_server.spl
  src/app/ui.web/tls_serve_loop.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`,
  and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- blocker: A live async-server launcher was attempted but the interpreter path
  fails before serving with existing `unknown extern function: rt_sqlite_open`;
  keep async live request-head evidence pending that separate launch/runtime
  issue.
- fix: Centralized browser JSON response security headers in
  `ui_web_json_security_headers` and reused them across normal, async, TLS,
  and shared `/ui/*` JSON response builders.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/auth_params.spl src/app/ui.web/server.spl
  src/app/ui.web/async_server.spl src/app/ui.web/tls_serve_loop.spl
  src/app/ui.web/ui_routes.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/01_unit/app/ui/async_web_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`,
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/async_web_spec.spl --mode=interpreter --clean`, and
  `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- fix: Applied the same `UI_WEB_MAX_REQUEST_HEAD_BYTES`,
  `UI_WEB_MAX_REQUEST_LINE_BYTES`, and `UI_WEB_MAX_HEADER_LINE_BYTES` guards to
  the normal `run_web` request-head parser that shared-WM already used.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/server.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passes,
  and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passes with normal-server and
  shared-WM oversized request-head coverage.
- fix: Replaced shared-WM `read_line` request-head accumulation with a bounded
  chunked parser using `UI_WEB_MAX_REQUEST_HEAD_BYTES`; oversized heads,
  request lines, and header lines return `413 Payload Too Large` before route
  dispatch.
- fix: Shared-WM `/ui/login` now consumes already-read request body bytes
  through the same bounded body helper used by other shared-WM POST routes.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/auth_params.spl src/app/ui.web/server.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`,
  and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- fix: Added `UI_WEB_MAX_WS_FRAME_BYTES` and shared
  `ui_web_ws_frame_payload_allowed` so normal TCP and shared `/ui/ws`
  WebSocket frame readers reject oversized declared payloads before allocation.
- verify: `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl src/app/ui.web/ui_routes.spl
  test/01_unit/app/ui/ws_handler_spec.spl`,
  `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl
  --mode=interpreter --clean`, and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- fix: Added sanitized `X-Request-Id` extraction for Simple Web auth paths and
  echoed it on login/resume JSON responses without accepting bearer-like values.
- verify: `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl
  --mode=interpreter --clean`, and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.

- fix: Resolved `test/01_unit/app/ui/async_web_spec.spl` conflict markers by
  keeping both JSON no-store/nosniff response coverage and HTML
  frame/referrer/CSP response coverage for the async server helper.
- verify: `bin/simple check test/01_unit/app/ui/async_web_spec.spl
  src/app/ui.web/async_server.spl src/app/ui.web/auth_params.spl` passes.
- verify: `bin/simple test test/01_unit/app/ui/async_web_spec.spl
  --mode=interpreter --clean` passes with 27 scenarios.
- docs: Resolved `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
  conflict markers in the coverage and traceability tables, keeping the
  stricter browser production evidence rows for deprecated query-token
  non-authorization, legacy `/ws` hiding, JSON/HTML security headers, sanitized
  request IDs, and normal/shared-WM/async/TLS request-boundary guards.
- verify: `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple sh
  scripts/check/check-production-gui-web-renderer-parity-evidence.shs` completed
  with top-level status `pass` and wrote
  `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-17.md`.
  Evidence: Electron generated GUI matrix `pass` for 80x64, 96x72, 128x96, and
  160x120 with zero mismatches; Electron CSS/layout manifest `pass` with 18
  cases, 16 exact passes, 2 tracked text-raster divergence cases, and 0
  failures; Tauri/Chrome surface manifest `pass` with Electron, Tauri, and
  Chrome captures all `pass`; backend CPU SIMD/Metal parity `pass` with exact
  backend parity and no blur/tolerance. Font offload/readback remains
  `unavailable` on this host due CUDA/runtime glyph-readback gaps; raw Metal
  framebuffer readback remains `unavailable` because Metal requires macOS.
- docs: Refreshed `doc/09_report/simple_web_browser_production_hardening.md`
  to reference the 2026-06-17 production renderer parity report and current
  async web unit pass.
- verify: `SIMPLE_LIB=src bin/simple spipe-docgen
  test/01_unit/app/ui/async_web_spec.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --output doc/06_spec --no-index` completed with existing doc-quality
  warnings and generated/refreshed 3 focused manuals. `find doc/06_spec -name
  '*_spec.spl' | wc -l` returned `0`.
- docs: Added the expected top-level architecture pipeline artifact
  `doc/04_architecture/simple_web_browser_production_hardening.md`, pointing to
  the detailed UI architecture note, and added the missing detail design
  artifact `doc/05_design/simple_web_browser_production_hardening.md` covering
  modules, fail-closed request handling, rendering evidence, traceability, and
  external host gates.
- verify: Focused artifact audit confirms the expected architecture/design
  paths exist, focused specs contain no conflict markers or placeholder passes,
  and `find doc/06_spec -name '*_spec.spl' | wc -l` remains `0`.
- tracking: Updated
  `doc/08_tracking/feature/feature_db.sdn` row
  `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16` to include the new
  top-level architecture artifact, detail design artifact, async unit spec,
  async generated manual, and 2026-06-17 evidence dates while preserving status
  `current` because external Metal, ROCm/HIP, DirectX, and browser WebGPU
  native-device proof remains open.
- verify: `bin/simple lint doc/08_tracking/feature/feature_db.sdn` passes.
- fix: Resolved focused browser production hardening conflict markers in
  `src/app/ui.web/auth_params.spl`, normal/async/TLS server response helpers,
  `test/01_unit/app/ui/web_auth_hardening_spec.spl`,
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`, and
  the hardening report, keeping the stricter request-boundary and browser
  document security-header behavior.
- verify: `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl src/app/ui.web/async_server.spl
  src/app/ui.web/tls_serve_loop.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passes.
- fix: Added the headless-safe Electron GPU flags already used by Engine2D
  bitmap evidence to `check-electron-simple-web-layout-bitmap-evidence.shs`,
  preventing Xvfb hosts from aborting with an unusable Chromium GPU process.
- verify: `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple sh
  scripts/check/check-electron-simple-web-layout-bitmap-evidence.shs` passes:
  status `pass`, zero mismatched pixels, captured ARGB written, Electron frame
  time `30788us`.
- fix: Centralized WebSocket upgrade method policy in
  `ui_web_ws_upgrade_method_allowed` and reused it in normal, async, and TLS
  transports so non-GET upgrade-shaped requests return `405 Method Not
  Allowed` before any WebSocket handshake.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/ws_handler.spl src/app/ui.web/__init__.spl
  src/app/ui.web/server.spl src/app/ui.web/async_server.spl
  src/app/ui.web/tls_serve_loop.spl test/01_unit/app/ui/ws_handler_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` and
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` pass.
- fix: Added shared `ui_web_html_security_headers` and reused it in normal,
  async, and TLS HTML response builders so browser documents carry anti-sniff,
  frame-deny, no-referrer, permissions, and restrictive CSP headers. Also fixed
  the normal root response's interpreter-visible `headers` const collision by
  renaming the mutable response header accumulator.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/auth_params.spl src/app/ui.web/server.spl
  src/app/ui.web/async_server.spl src/app/ui.web/tls_serve_loop.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/01_unit/app/ui/async_web_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`,
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/async_web_spec.spl --mode=interpreter --clean`, and
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- fix: Added shared request-body framing validation before normal, shared-WM,
  async, and TLS POST body reads. Duplicate `Content-Length`, malformed or
  signed lengths, and any `Transfer-Encoding` now fail closed with
  `400 Bad Request`; valid oversized lengths still return `413 Payload Too
  Large`.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/auth_params.spl src/app/ui.web/server.spl
  src/app/ui.web/async_server.spl src/app/ui.web/tls_serve_loop.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `/home/ormastes/dev/pub/simple/bin/simple test
  test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`,
  and `/home/ormastes/dev/pub/simple/bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- fix: Retired legacy WebSocket compatibility in production by allowing upgrade
  routing only for `/ui/ws`, returning `404 Not Found` for `/ws` and arbitrary
  upgrade-shaped routes across normal, async, and TLS transports, switching
  generated browser JS to the canonical `/ui/ws` URL, and making deprecated
  query-token env opt-in non-authorizing.
- verify: `/home/ormastes/dev/pub/simple/bin/simple check
  src/app/ui.web/auth_params.spl src/app/ui.web/ws_handler.spl
  src/app/ui.web/__init__.spl src/app/ui.web/server.spl
  src/app/ui.web/async_server.spl src/app/ui.web/tls_serve_loop.spl
  src/app/ui.web/html.spl test/01_unit/app/ui/ws_handler_spec.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/02_integration/app/ui.web/ws_e2e_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  focused unit/integration specs, live hardening system spec, docgen, and
  `find doc/06_spec -name '*_spec.spl' | wc -l` pass.
- verify: Refreshed local GPU/environment evidence with absolute
  `SIMPLE_BIN=/home/ormastes/dev/pub/simple/bin/simple`: Vulkan Engine2D
  readback `pass`, host-GPU queue/readback aggregate `pass` with same-frame
  Vulkan/BrowserBackend device readback, Metal and ROCm generated readback
  `unavailable` due missing host/toolchain, and WebGPU real readback
  `unavailable` with `source=not_device_readback`.
- docs: Corrected final feature/NFR option candidates so user selection matches
  current production behavior: canonical `/ui/ws` upgrades are bearer-gated,
  legacy `/ws` is hidden, and deprecated query-token env opt-in is
  non-authorizing.
- docs: Recorded user selection of Feature Option C and NFR Option C, wrote
  final requirement documents, deleted unselected option files, and backfilled
  selected `REQ-WEB-HARD-*` / `NFR-WEB-HARD-*` trace IDs into executable specs,
  generated manuals, the system-test plan, reports, and the feature tracking
  row. External host proof for macOS Metal, AMD ROCm/HIP, Windows DirectX, and
  real browser WebGPU device readback remains open.
- docs: Updated
  `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md` with a
  fresh-session plan for continuing from crashed rollout
  `019e85dc-fb0c-73b0-b0c6-2a6ead9624ed` without resuming it. The active audit
  artifact is
  `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`;
  remaining work is external host proof or explicit host-blocker reporting.
- evidence: Probed the current host for the external proof prerequisites and
  wrote `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md`.
  The host is Linux, lacks macOS Metal tools/frameworks, lacks ROCm/HIP tools,
  and lacks Windows PowerShell/DirectX proof environment. The feature remains
  `current`; this report is blocker evidence and does not close
  `REQ-WEB-HARD-014` or `NFR-WEB-HARD-012`.
- fix: Added sanitized `X-Request-Id` extraction for Simple Web auth paths and
  echoed it on login/resume JSON responses without accepting bearer-like values.
- verify: `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl
  --mode=interpreter --clean`, and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- fix: Replaced shared-WM `read_line` request-head accumulation with a bounded
  chunked parser using `UI_WEB_MAX_REQUEST_HEAD_BYTES`; oversized heads return
  `413 Payload Too Large` before route dispatch.
- verify: `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl`,
  `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl
  --mode=interpreter --clean`, and `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` pass.
- verify: Re-ran `bin/simple test
  test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`
  on 2026-06-17 after adding request-head boundary coverage for shared-WM route
  dispatch; the focused auth hardening spec passed with 20 scenarios.
- fix: Added `ui_web_script_security_headers` and applied no-store/nosniff
  guards to normal-server `/wm.js` and `/retained_renderer.js` responses.
  Also applied existing JSON no-store/nosniff guards to successful normal-server
  `/api/state` and `/api/widgets` responses, closing a static script/API
  success-path hardening gap.
- verify: `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl`
  passed after the static script/API header hardening patch.
- verify: Re-ran `bin/simple test
  test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean`
  after adding static script-header coverage; the focused auth hardening spec
  passed with 21 scenarios. A focused scan of async/TLS/static response paths
  found no additional async or TLS JavaScript-serving path beyond the normal
  server and shared `_simple_response` routes already covered by the patch.
- verify: Confirmed
  `doc/06_spec/test/01_unit/app/ui/web_auth_hardening_spec.md` is newer than
  `test/01_unit/app/ui/web_auth_hardening_spec.spl` and contains the browser
  script-header scenario. Ran `find doc/06_spec -name '*_spec.spl' | wc -l`;
  it returned `0`.
- test: Added a live `/wm.js` request to
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` so the
  production endpoint spec verifies no-store, Pragma, and nosniff headers on an
  actual static script HTTP response.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios after the
  live static-script header assertion.
- verify: Confirmed
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  is newer than `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
  and contains the live `/wm.js` no-store/nosniff assertions. Ran
  `find doc/06_spec -name '*_spec.spl' | wc -l`; it returned `0`.
- docs: Refreshed `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
  so the executable coverage and `NFR-WEB-HARD-003` traceability include
  JSON/static-script no-store/nosniff response header evidence.
- docs: Updated the
  `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16` feature DB row to name
  JSON/static-script response header hardening and include
  `src/app/ui.web/retained_renderer.js` in the implementation artifact list.
- verify: `bin/simple lint doc/08_tracking/feature/feature_db.sdn` passed after
  the traceability refresh.
- verify: `bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/server.spl
  test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passed
  after the static script/API header hardening and live `/wm.js` assertion
  changes.
- test: Added a live `/retained_renderer.js` request to
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` so the
  production endpoint spec verifies no-store, Pragma, and nosniff headers on
  both static browser script responses.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios after the
  retained renderer static-script header assertion.
- docs: Regenerated
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  with `SIMPLE_LIB=src bin/simple spipe-docgen
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index`; docgen completed with existing generator/manual
  quality warnings and the manual now includes `/retained_renderer.js`
  no-store/nosniff evidence.
- docs: Updated
  `doc/03_plan/sys_test/simple_web_browser_production_hardening.md` and the
  main hardening report so static-script traceability explicitly names both
  `/wm.js` and `/retained_renderer.js` live no-store/nosniff evidence.
- docs: Updated
  `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md` so the
  fresh-session handoff includes the static script/API header hardening,
  retained renderer live proof, generated manual refresh, focused check, and
  feature DB lint evidence.
- verify: Added
  `doc/09_report/simple_web_browser_local_completion_audit_2026-06-17.md`.
  The audit records local PASS coverage for `REQ-WEB-HARD-001` through
  `REQ-WEB-HARD-013` and `NFR-WEB-HARD-001` through `NFR-WEB-HARD-011`, with
  WARN status for external `REQ-WEB-HARD-014` and `NFR-WEB-HARD-012`
  device-readback proof.
- fix: Replaced the fallback UI parse `pass_do_nothing` in
  `src/app/ui.web/server.spl` with explicit error propagation.
- verify: `bin/simple check src/app/ui.web/server.spl` passed. A focused stub
  scan over `src/app/ui.web/auth_params.spl`, `src/app/ui.web/server.spl`,
  `test/01_unit/app/ui/web_auth_hardening_spec.spl`, and
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` returned
  no matches for placeholder/stub patterns.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios after the
  fallback parse error handling change in `src/app/ui.web/server.spl`.
- verify: `bin/simple check src/app/ui.web/auth_params.spl
  src/app/ui.web/server.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passed
  after the fallback parse error handling change and static-script hardening
  updates.
- verify: `sh scripts/audit/numbered-artifact-guard.shs --working` returned
  `Numbered artifact guard: OK`.
- verify: `sh scripts/audit/numbered-artifact-guard.shs --staged` returned
  `Numbered artifact guard: OK`.
- verify: Focused SPipe-quality scan over
  `test/01_unit/app/ui/web_auth_hardening_spec.spl` and
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` returned
  no matches for placeholder assertions, deprecated truthy helpers, no-op
  placeholders, TODO/FIXME markers, or `pass_todo`.
- docs: Added an external-host evidence manifest to
  `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md` so
  the remaining Metal, ROCm/HIP, DirectX, and browser WebGPU native readback
  gates have explicit status/source/handle/report fields for the next host run.
- docs: Aligned `doc/05_design/simple_web_browser_production_hardening.md` with
  the current static browser script hardening by naming `retained_renderer.js`
  alongside `wm.js` and documenting no-store/no-cache/nosniff script headers.
- docs: Aligned
  `doc/04_architecture/ui/simple_web_browser_production_hardening.md` with the
  current browser-client boundary by naming `retained_renderer.js` and adding a
  response-header boundary for successful JSON plus static script responses.
- docs: Updated
  `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` to require
  the external-host Evidence Manifest fields from the runbook for every
  remaining Metal, ROCm/HIP, DirectX, and browser WebGPU readback run.
- docs: Added
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
  and linked it from the external-host proof runbook so each remaining native
  rendering proof has a consistent fillable evidence handoff.
- docs: Linked the external-host evidence manifest template from
  `doc/09_report/simple_web_browser_production_hardening.md` so the main
  production hardening report points to the same required closure artifact as
  the external-host runbook.
- docs: Updated
  `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md` so the
  fresh-session stop condition explicitly uses the external-host evidence
  manifest template for any completed Metal, ROCm/HIP, DirectX, or browser
  WebGPU native readback proof.
- docs: Clarified placeholder external report paths in
  `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md` as
  filename patterns so mechanical link checks do not treat undated future Metal
  and ROCm/HIP report names as missing current artifacts.
- docs: Expanded
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
  with a per-gate field checklist for Metal, ROCm/HIP, DirectX, and browser
  WebGPU so external proof submissions include the exact runbook status/source
  fields.
- docs: Updated
  `doc/09_report/simple_web_browser_local_completion_audit_2026-06-17.md` so
  the remaining-release-blocker section points to the external-host evidence
  manifest template as the required capture format for native readback results.
- docs: Added
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
  to the `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16` feature DB
  plan/handoff artifact list so tracking includes the external proof template.
- docs: Updated the fresh-session ownership note in
  `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md` so the
  external host evidence manifest template is explicitly in this lane's proof
  handoff scope.
- docs: Updated
  `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md` so the
  current-host blocker points future external runs to the evidence manifest
  template instead of only the runbook.
- docs: Updated
  `doc/03_plan/sys_test/simple_web_browser_production_hardening.md` so the GPU
  matrix, `REQ-WEB-HARD-014`, `NFR-WEB-HARD-012`, and release blocker note
  reference the external-host proof runbook plus evidence manifest template.
- docs: Aligned
  `doc/04_architecture/ui/simple_web_browser_production_hardening.md` and
  `doc/05_design/simple_web_browser_production_hardening.md` with the external
  evidence manifest template requirement for remaining native rendering gates.
- evidence: Re-probed the current Linux host for remaining external rendering
  gate prerequisites and refreshed
  `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md`; Metal
  tools/framework, ROCm/HIP tools, and Windows PowerShell/DirectX proof
  environment remain unavailable locally.
- docs: Added the concrete external-host evidence manifest template path to
  `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` after the
  final blocker audit found the matrix listed the fields but not the template
  artifact.
- tracking: Added a dedicated external-native-readback follow-up plan, feature
  request, todo entry, and blocked feature DB row because this Linux host cannot
  produce macOS Metal, AMD ROCm/HIP, Windows DirectX, or real browser WebGPU
  native `device_readback` evidence.
- docs: Linked the blocked
  `SIMPLE_WEB_BROWSER_EXTERNAL_NATIVE_READBACK_PROOF_2026_06_17` follow-up from
  `doc/09_report/simple_web_browser_production_hardening.md` so the parent
  production report points to the new plan and request.
- docs: Updated
  `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md` so the
  parent handoff directs future external native readback work through the
  blocked `SIMPLE_WEB_BROWSER_EXTERNAL_NATIVE_READBACK_PROOF_2026_06_17`
  follow-up feature and plan.
- docs: Added the
  `SIMPLE_WEB_BROWSER_EXTERNAL_NATIVE_READBACK_PROOF_2026_06_17` feature ID to
  `doc/03_plan/agent_tasks/simple_web_browser_external_native_readback_proof.md`
  so the external proof plan is self-identifying.
- fix: Added `/retained_renderer.js` handling to the separate shared-WM server
  path in `src/app/ui.web/server.spl`, so shared-WM mode exposes the same
  hardened retained renderer script surface as the normal server.
- test: Extended
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` shared-WM
  live coverage to fetch `/wm.js` and `/retained_renderer.js` and assert
  no-store/nosniff script headers, including a 200 response for the retained
  renderer path.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios after the
  shared-WM retained renderer route and system-spec assertions.
- docs: Regenerated
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  with `SIMPLE_LIB=src bin/simple spipe-docgen
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index`; docgen completed with existing manual-quality
  warnings and includes shared-WM browser script response evidence.
- test: Tightened shared-WM static browser script evidence so `/wm.js` and
  `/retained_renderer.js` must both include `Pragma: no-cache` in addition to
  `Cache-Control: no-store` and `X-Content-Type-Options: nosniff`.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios after the
  shared-WM script-cache parity assertions.
- docs: Regenerated
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  after the shared-WM `Pragma: no-cache` assertions; docgen completed with the
  existing 5 manual-quality warnings and the generated manual contains the new
  shared retained-renderer script evidence.
- docs: Expanded the executable
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
  manual source with plan, design, architecture, research, syntax, examples,
  and production evidence scope sections so the generated browser hardening
  manual is reviewable without relying on folded code.
- verify: `SIMPLE_LIB=src bin/simple spipe-docgen
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index` now reports
  `OK simple_web_browser_production_hardening_spec (115 lines)` with no
  spec-manual warnings; a focused artifact check confirmed source/generated
  docs contain the expected links and no conflict markers.
- verify: `bin/simple check
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passes
  after the executable spec manual-quality expansion.
- fix: Routed normal and shared-WM unknown-route 404 fallbacks through
  `_simple_response(404, "application/json", "{\"error\": \"not_found\"}")`
  instead of ad hoc plain-text responses, so hidden browser routes inherit the
  JSON no-store/no-cache/nosniff hardening headers.
- test: Added live normal and shared-WM unknown-route requests to
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` and
  asserted 404 `not_found` plus `Cache-Control: no-store`,
  `Pragma: no-cache`, and `X-Content-Type-Options: nosniff`.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios after the
  hidden-route fallback hardening.
- docs: Regenerated
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  after the hidden-route fallback assertions and expanded the executable manual
  prose to name `/hidden-browser-production-gap` and `{"error": "not_found"}`.
- verify: `SIMPLE_LIB=src bin/simple spipe-docgen
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index` reports
  `OK simple_web_browser_production_hardening_spec (124 lines)`; a focused
  generated-manual check found the hidden-route fallback evidence and no
  conflict markers.
- docs: Updated
  `doc/03_plan/sys_test/simple_web_browser_production_hardening.md` and
  `doc/09_report/simple_web_browser_production_hardening.md` so the
  release-facing traceability names the normal/shared-WM
  `/hidden-browser-production-gap` JSON `404 not_found` fallback and the clean
  124-line generated manual.
- verify: Focused artifact validation confirmed the system test plan,
  production report, generated live endpoint manual, and state log all contain
  the hidden-route fallback evidence and have no conflict markers.
- verify: `bin/simple check src/app/ui.web/server.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passes
  after the hidden-route JSON fallback implementation and executable spec
  updates.
- test: Added live `/wm/native_window?app_id=browser-hardening` coverage to
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` for
  both normal and shared-WM server paths, asserting `200 OK` plus
  `X-Frame-Options: DENY`, `Referrer-Policy: no-referrer`, and restrictive
  `Content-Security-Policy` headers on the shown native-window HTML surface.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed with 6 scenarios after the
  native-window route header assertions.
- docs: Regenerated
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  after the native-window route assertions.
- verify: `SIMPLE_LIB=src bin/simple spipe-docgen
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index` reports
  `OK simple_web_browser_production_hardening_spec (125 lines)`; focused
  validation confirmed the source spec, generated manual, and state log contain
  native-window evidence and no conflict markers.
- docs: Updated
  `doc/03_plan/sys_test/simple_web_browser_production_hardening.md` and
  `doc/09_report/simple_web_browser_production_hardening.md` so release-facing
  traceability names `/wm/native_window` as a shown browser HTML surface covered
  by the normal and shared-WM live endpoint evidence.
- verify: Focused artifact validation confirmed the system test plan,
  production report, generated live endpoint manual, and state log contain the
  `/wm/native_window` evidence and have no conflict markers.
- verify: `bin/simple check src/app/ui.web/server.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passes
  after the native-window live coverage and traceability updates.
- docs: Replaced the stale `doc/09_report/simple_web_browser_production_hardening.md`
  spec-docgen line that still mentioned existing warnings with the current
  `OK simple_web_browser_production_hardening_spec (125 lines)` result and
  explicit `/wm/native_window` plus hidden-route fallback evidence.
- verify: Focused artifact validation confirmed the production report,
  generated live endpoint manual, and state log contain the current 125-line
  docgen result, native-window evidence, hidden-route fallback evidence, and no
  conflict markers.
- docs: Updated `doc/05_design/simple_web_browser_production_hardening.md` and
  `doc/04_architecture/ui/simple_web_browser_production_hardening.md` so design
  and architecture name the shown `/wm/native_window` HTML surface,
  normal/shared-WM static script surfaces, and unknown-route JSON
  `404 not_found` fallback covered by the live endpoint evidence.
- verify: Focused artifact validation confirmed the detail design, UI
  architecture, and generated live endpoint manual contain the native-window and
  hidden-route evidence and have no conflict markers.
- docs: Updated `doc/04_architecture/simple_web_browser_production_hardening.md`
  and `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md` so
  the top-level architecture and handoff name the current local browser-surface
  evidence: `/wm.js`, `/retained_renderer.js`, `/wm/native_window`, unknown-route
  JSON `404 not_found` fallback, and clean 125-line live endpoint manual.
- verify: Focused artifact validation confirmed the top-level architecture,
  agent handoff, generated live endpoint manual, and state log contain the
  current browser-surface evidence and have no conflict markers.
- impl: Centralized the normal server `/wm.js` and `/retained_renderer.js`
  responses through `_simple_response(200, "application/javascript", ...)` in
  `src/app/ui.web/server.spl`, matching the shared-WM static script path so both
  shown server modes use the same no-store/no-cache/nosniff header helper.
- verify: `bin/simple check src/app/ui.web/server.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passed
  after the normal static script response convergence.
- impl: Centralized the normal server root HTML response and authenticated
  `/api/state` plus `/api/widgets` JSON responses through `_simple_response`,
  removing the remaining hand-built success headers from the normal browser
  route block so shown HTML, API JSON, static script, native-window, and hidden
  fallback responses share the same security-header policy helper.
- verify: `bin/simple check src/app/ui.web/server.spl
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl` passed
  after the normal HTML/API response convergence.
- test: Added live authenticated `/api/state` and `/api/widgets` success-path
  checks to `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
  so shown API JSON surfaces now prove `200 OK` plus no-store/no-cache/nosniff
  headers after the response-helper convergence.
- verify: `bin/simple check test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  src/app/ui.web/server.spl` passed after adding authenticated API success-header
  coverage.
- docs: Regenerated
  `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md`
  after adding authenticated `/api/state` and `/api/widgets` success-header
  coverage.
- verify: `SIMPLE_LIB=src bin/simple spipe-docgen
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output
  doc/06_spec --no-index` reported
  `OK simple_web_browser_production_hardening_spec (125 lines)` and the generated
  manual now contains the authenticated API `200 OK` plus no-store/no-cache/nosniff
  assertions.
- verify: `bin/simple test
  test/03_system/gui/simple_web_browser_production_hardening_spec.spl
  --mode=interpreter --clean --timeout 360` passed all 6 live scenarios after the
  authenticated `/api/state` and `/api/widgets` success-header assertions.
- docs: Updated `doc/03_plan/sys_test/simple_web_browser_production_hardening.md`
  so the system-test plan names the live authenticated `/api/state` and
  `/api/widgets` `200 OK` plus no-store/no-cache/nosniff evidence and the
  regenerated manual coverage.
- docs: Updated `doc/09_report/simple_web_browser_production_hardening.md` so the
  production report's current evidence and hardening summary name the
  authenticated `/api/state` and `/api/widgets` success-path header assertions.
- docs: Updated the `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16` row in
  `doc/08_tracking/feature/feature_db.sdn` so feature tracking names the
  authenticated `/api/state` and `/api/widgets` `200 OK` JSON
  no-store/no-cache/nosniff evidence.
- docs: Updated `doc/09_report/simple_web_browser_local_completion_audit_2026-06-17.md`
  so the local completion audit includes the authenticated `/api/state` and
  `/api/widgets` success-header evidence while preserving the external native
  proof WARN.
- docs: Updated `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md`
  so the handoff names the authenticated `/api/state` and `/api/widgets`
  success-header evidence and uses no-store/no-cache/nosniff wording for JSON and
  script response guards.
- docs: Updated `doc/04_architecture/simple_web_browser_production_hardening.md`
  so the top-level architecture summary includes authenticated `/api/state` and
  `/api/widgets` `200 OK` JSON response evidence alongside script, native-window,
  and hidden-route fallback evidence.
- docs: Updated `doc/04_architecture/ui/simple_web_browser_production_hardening.md`
  so the detailed response-header boundary names authenticated `/api/state` and
  `/api/widgets` `200 OK` responses as part of the no-store/no-cache/nosniff
  browser boundary.
- docs: Updated `doc/05_design/simple_web_browser_production_hardening.md` so the
  detail design response-header algorithm names authenticated `/api/state` and
  `/api/widgets` `200 OK` JSON responses alongside JSON error, hidden fallback,
  static script, and HTML document surfaces.
- docs: Normalized stale no-store/nosniff wording to
  no-store/no-cache/nosniff in `doc/09_report/simple_web_browser_production_hardening.md`
  and `doc/03_plan/agent_tasks/simple_web_browser_production_hardening.md`.
- audit: Re-inspected `src/app/ui.web/server.spl` response assembly after the
  helper convergence. Remaining manual `HTTP/1.1` strings are limited to the
  WebSocket `101 Switching Protocols` handshake and `_simple_response` itself;
  direct browser document, API JSON, static script, native-window, and hidden
  fallback route bodies now flow through the shared response helper.
- docs: Updated
  `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md` with the
  current local browser-hardening baseline before external host handoff:
  authenticated API JSON, script, native-window, hidden fallback, and 6-scenario
  live endpoint evidence are local PASS; native device readback remains external.
- docs: Updated `doc/03_plan/agent_tasks/simple_web_browser_external_native_readback_proof.md`
  with the same current local PASS baseline so external host runners focus on
  native device readback evidence rather than rerunning local browser route
  convergence.
- docs: Updated
  `doc/08_tracking/todo/simple_web_browser_external_native_readback_proof_2026-06-17.md`
  with the local PASS baseline so the external TODO tracks only native readback
  proof work.
- docs: Updated
  `doc/08_tracking/feature/simple_web_browser_external_native_readback_proof_2026-06-17.md`
  with the same concrete local PASS baseline before external native readback
  handoff.
- docs: Updated `doc/08_tracking/feature/feature_db.sdn` to use the literal
  `/wm/native_window` route name in the parent browser-hardening feature row,
  matching the rest of the focused local PASS evidence artifacts.
- docs: Updated `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`
  with the 2026-06-17 local browser hardening baseline so the GPU matrix clearly
  separates local route/header PASS evidence from external native readback gaps.
