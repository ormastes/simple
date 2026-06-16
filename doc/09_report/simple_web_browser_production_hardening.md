# Simple Web Browser Production Hardening Report

## Current Evidence

- Auth/parser check: focused `bin/simple check` passed for `server.spl`,
  `tls_serve_loop.spl`, `async_server.spl`,
  `simple_web_browser_production_hardening_spec.spl`,
  `web_auth_hardening_spec.spl`, and `ws_handler_spec.spl`.
- Unit auth spec: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passed with 19 scenarios.
- Unit async web spec: `bin/simple test test/01_unit/app/ui/async_web_spec.spl --mode=interpreter --clean` passed with 27 scenarios.
- Unit WebSocket helper spec: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` passed with 12 scenarios.
- Live endpoint spec: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360` passed with 6 scenarios.
- Spec docgen: `bin/simple spipe-docgen test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output doc/06_spec` completed with existing docgen warnings and regenerated the 6-scenario manual.
- Production renderer parity: `sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs` passed.
- Layout guard: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

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
- Browser HTML document response helpers across normal, async, and TLS paths
  set `X-Content-Type-Options: nosniff`, `X-Frame-Options: DENY`,
  `Referrer-Policy: no-referrer`, `Permissions-Policy`, and a restrictive
  `Content-Security-Policy`; the live root-page socket scenario covers the
  normal server response.
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
- Production renderer parity wrapper now passes locally with surface fail counts
  `0`.

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

## Workspace Hygiene Evidence

Snapshot from 2026-06-16:

- `jj --no-pager status` reports unrelated working-copy changes outside this
  lane: 107 tracked changes (`A=66`, `M=39`, `D=2`) plus 5 untracked example
  roots. Representative unrelated paths include
  `.spipe/ide_md_counter_office_hardening/state.md`,
  `doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md`,
  `bootstrap/stage1/simple`, and `examples/08_gpu/simple_cuda_example/`.
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
