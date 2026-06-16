# Simple Web Browser Production Hardening Report

## Current Evidence

- Auth/parser check: focused `bin/simple check` passed for `server.spl`,
  `tls_serve_loop.spl`, `async_server.spl`,
  `simple_web_browser_production_hardening_spec.spl`,
  `web_auth_hardening_spec.spl`, and `ws_handler_spec.spl`.
- Unit auth spec: `bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean` passed with 14 scenarios.
- Unit WebSocket helper spec: `bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean` passed with 10 scenarios.
- Live endpoint spec: `bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360` passed with 5 scenarios.
- Spec docgen: `bin/simple spipe-docgen test/03_system/gui/simple_web_browser_production_hardening_spec.spl --output doc/06_spec` completed with existing docgen warnings and regenerated the 5-scenario manual.
- Production renderer parity: `sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs` passed.
- Layout guard: `find doc/06_spec -name '*_spec.spl' | wc -l` returned `0`.

## Implemented Hardening

- Production token secrets fail closed unless explicitly opted into local
  non-TLS dev fallback.
- TLS mode never uses the insecure dev secret.
- Login origin checks fail closed before token minting.
- `/ui/ws`, legacy `/ws`, `/ui/resume`, and sensitive `/api/*` require
  origin-bound bearer authorization.
- Authorized `/ui/resume` rejects missing or malformed `session_id`,
  `snapshot_revision`, or `last_sequence` with `400 Bad Request`, and accepts
  strict valid body fields in the normal TCP server path.
- Generated browser clients and static `wm.js` use WebSocket subprotocol bearer
  tokens instead of query-string tokens.
- Query-string bearer compatibility is disabled by default behind
  `SIMPLE_UI_WEB_ALLOW_QUERY_TOKEN=1`, and the live endpoint spec proves the
  opt-in path can redeem a minted origin-bound token.
- `/ui/login` is bounded by a fixed-window burst gate in both normal and shared
  WM server paths.
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
  `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`.
- macOS Metal is host-unavailable locally and must be proven on macOS.
- AMD ROCm/HIP is host-unavailable locally and must be proven on an AMD ROCm
  host.

## Remaining Release Work

- User selection of final feature and NFR options is still required before
  writing final `REQ-*` and `NFR-*` files.
- Requirement trace IDs need to be added to executable specs after final
  requirements exist.
- `doc/08_tracking/feature/feature_db.sdn` has a `current` row for this lane;
  do not mark it `done` until final requirements, trace IDs, and macOS
  Metal/AMD ROCm host evidence are complete.
