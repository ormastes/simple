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
| Case-insensitive WebSocket upgrade headers and comma-token `Connection` parsing | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| Non-GET WebSocket upgrade rejection for `/ui/ws` and legacy `/ws` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Warm login plus authenticated WebSocket upgrade latency | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | measured locally with a 10s ceiling |
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

## Pre-Selection Traceability Matrix

Final `REQ-WEB-HARD-*` and `NFR-WEB-HARD-*` files remain pending explicit user
selection. Until then, use this matrix to keep every candidate ID tied to its
current evidence artifact without promoting unselected scope.

| Candidate ID | Evidence Artifact | Evidence Status |
|--------------|-------------------|-----------------|
| `REQ-WEB-HARD-001` | `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-002` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `src/app/ui.web/tls_serve_loop.spl` check | passing |
| `REQ-WEB-HARD-003` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-004` | `src/app/ui.web/server.spl`; `src/app/ui.web/ui_routes.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-005` | `src/app/ui.web/wm.js`; `test/01_unit/app/ui/ws_handler_spec.spl`; query-token default-off live evidence | passing |
| `REQ-WEB-HARD-006` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-007` | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; generated manual `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md` | passing |
| `REQ-WEB-HARD-008` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-009` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-010` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` child-process cleanup path | passing |
| `REQ-WEB-HARD-011` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` normal and shared-WM burst scenarios | passing |
| `REQ-WEB-HARD-012` | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-013` | `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`; `doc/09_report/simple_web_browser_production_hardening.md` | passing locally |
| `REQ-WEB-HARD-014` | `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` | partial: Linux local evidence recorded; Metal/ROCm/DirectX/WebGPU native device-readback requires external hosts |
| `NFR-WEB-HARD-001` | `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passing |
| `NFR-WEB-HARD-002` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; TLS server check | passing |
| `NFR-WEB-HARD-003` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `NFR-WEB-HARD-004` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `NFR-WEB-HARD-005` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; body-size guards in `src/app/ui.web/server.spl` and `src/app/ui.web/ui_routes.spl` | passing |
| `NFR-WEB-HARD-006` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` process start/kill helpers | passing |
| `NFR-WEB-HARD-007` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` warm auth latency scenario | measured locally with a 10s ceiling; final target still requires selection |
| `NFR-WEB-HARD-008` | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; generated manual | passing |
| `NFR-WEB-HARD-009` | `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` | passing locally |
| `NFR-WEB-HARD-010` | `src/app/ui.web/wm.js`; `test/01_unit/app/ui/ws_handler_spec.spl`; live query-token compatibility scenario | passing |
| `NFR-WEB-HARD-011` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `NFR-WEB-HARD-012` | `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` | partial: explicit status rows exist; native Metal/ROCm/DirectX/WebGPU device-readback requires external hosts |

After final requirement selection, add the selected candidate IDs to the
executable specs and generated manuals, then delete unselected option files.

## Release Blockers

- Final requirement and NFR files are not selected/written.
- Metal, AMD ROCm, DirectX, and WebGPU native proof require external host
  environments.
- AC-7 hygiene evidence must be current at handoff; unrelated dirty files and
  existing `jj` conflicts remain separate from this lane.
