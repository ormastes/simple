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
6. Follow-up production slices: gate sensitive `/api/*` readback/introspection routes, replace brittle ad hoc JSON/query parsing on auth paths, and run the full renderer parity wrapper once the shared checkout conflict is resolved.

## Phase

implementation

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
