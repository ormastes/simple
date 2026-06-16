# Simple Web Browser Production Hardening System Test Plan

## Status

Snapshot: 2026-06-16. Current plan maps the implemented hardening behavior to
executable evidence. Final `REQ-*` and `NFR-*` trace IDs remain pending
requirement selection.

## Executable Coverage

| Surface | Evidence | Current Status |
|---------|----------|----------------|
| Secret policy, origin guard, login burst gate | `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passing |
| Bearer extraction and query-token compatibility gate | `test/01_unit/app/ui/ws_handler_spec.spl` | passing |
| Live `/ui/login`, `/api/state`, `/ui/ws` fail-closed behavior | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Positive token mint and WebSocket upgrade | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Renderer parity gate | `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` | passing |
| GPU environment matrix | `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md` | Linux Vulkan/CUDA/OpenCL pass; Metal/ROCm host-unavailable; host-GPU queue first-render budget remains a follow-up |

## Required Commands

```sh
bin/simple check src/app/ui.web/auth_params.spl src/app/ui.web/ui_routes.spl src/app/ui.web/server.spl src/app/ui.web/ws_handler.spl test/01_unit/app/ui/ws_handler_spec.spl test/01_unit/app/ui/web_auth_hardening_spec.spl
bin/simple test test/01_unit/app/ui/ws_handler_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/app/ui/web_auth_hardening_spec.spl --mode=interpreter --clean
bin/simple test test/03_system/gui/simple_web_browser_production_hardening_spec.spl --mode=interpreter --clean --timeout 180
sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs
find doc/06_spec -name '*_spec.spl' | wc -l
```

## Traceability Work

After final requirement selection, add `REQ-*` and `NFR-*` tags to:

- `test/01_unit/app/ui/web_auth_hardening_spec.spl`
- `test/01_unit/app/ui/ws_handler_spec.spl`
- `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`
- generated manuals under `doc/06_spec/test/...`

## Release Blockers

- Final requirement and NFR files are not selected/written.
- Metal and AMD ROCm native proof require external host environments.
