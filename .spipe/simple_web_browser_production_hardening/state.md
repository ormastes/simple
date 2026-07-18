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
