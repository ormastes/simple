# Simple Web Browser Production Hardening System Test Plan

## Status

Snapshot: 2026-06-16. Current plan maps the implemented hardening behavior to
executable evidence. Candidate `REQ-WEB-HARD-*` and `NFR-WEB-HARD-*` IDs are
predeclared in the option docs; final trace backfill remains pending explicit
user selection.

## Executable Coverage

| Surface | Evidence | Current Status |
|---------|----------|----------------|
| Secret policy, origin guard, login burst gate | `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passing |
| Bearer extraction and query-token compatibility gate | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing, including live opt-in query-token upgrade |
| Live `/ui/login`, `/api/state`, `/api/widgets`, `/ui/resume`, `/ui/ws`, legacy `/ws`, and query-token `/ui/ws` fail-closed behavior | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Authorized `/ui/resume` malformed-body rejection and valid-body acceptance | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Positive token mint plus `/ui/ws` and legacy `/ws` WebSocket upgrades | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Non-GET WebSocket upgrade rejection for `/ui/ws` and legacy `/ws` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Live `/ui/login` fixed-window burst gate | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Live shared-WM `/ui/login` fixed-window burst gate | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Renderer parity gate | `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` | passing |
| GPU environment matrix | `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` | Linux Vulkan/CUDA/OpenCL pass; Metal/ROCm/DirectX/WebGPU native device-readback still external/partial |

## Required Commands

```sh
bin/simple check src/app/ui.web/server.spl src/app/ui.web/tls_serve_loop.spl src/app/ui.web/async_server.spl test/03_system/gui/simple_web_browser_production_hardening_spec.spl test/01_unit/app/ui/ws_handler_spec.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 360
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
jj --no-pager status
jj --no-pager log -r 'conflicts()' --no-graph --template 'change_id.short() ++ " " ++ commit_id.short() ++ " " ++ description.first_line() ++ "\n"'
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Workspace Hygiene Evidence

AC-7 requires this lane to report unrelated dirty files and existing `jj`
conflicts separately. Refresh the two `jj` commands above during verification
and record the snapshot in `doc/09_report/simple_web_browser_production_hardening.md`.
The browser-hardening lane must not absorb unrelated dirty files or conflict
cleanup unless explicitly requested.

## Traceability Work

After final requirement selection, add the selected `REQ-WEB-HARD-*` and
`NFR-WEB-HARD-*` tags to:

- `test/01_unit/app/ui/web_auth_hardening_spec.spl`
- `test/01_unit/app/ui/ws_handler_spec.spl`
- `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
- generated manuals under `doc/06_spec/test/...`

## Release Blockers

- Final requirement and NFR files are not selected/written.
- Metal and AMD ROCm native proof require external host environments.
- AC-7 hygiene evidence must be current at handoff; unrelated dirty files and
  existing `jj` conflicts remain separate from this lane.
