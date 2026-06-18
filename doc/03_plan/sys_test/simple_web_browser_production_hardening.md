# Simple Web Browser Production Hardening System Test Plan

## Status

Snapshot: 2026-06-17. Current plan maps the implemented hardening behavior to
executable evidence. Selected Feature Option C `REQ-WEB-HARD-*` and NFR Option
C `NFR-WEB-HARD-*` IDs are recorded in the final requirement documents and
traced below.

## Executable Coverage

| Surface | Evidence | Current Status |
|---------|----------|----------------|
| Secret policy, origin guard, login burst gate | `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passing |
| Bearer extraction and query-token compatibility gate | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing, including deprecated env non-authorization |
| Live `/ui/login`, `/api/state`, `/api/widgets`, `/ui/resume`, `/ui/ws`, legacy `/ws`, query-token `/ui/ws`, `/wm.js`, `/retained_renderer.js`, `/wm/native_window`, and unknown-route fallback behavior | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; `/api/clients` unit policy coverage in `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passed locally on 2026-06-17; legacy `/ws` hidden with 404; authenticated `/api/state` and `/api/widgets` success paths verify `200 OK` plus no-store/no-cache/nosniff headers; live normal-server and shared-WM `/wm.js`, `/retained_renderer.js`, `/wm/native_window`, and unknown-route fallback headers verified |
| Browser JSON and static script response cache-control and anti-sniff headers | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/01_unit/app/ui/async_web_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md` | passing, including live authenticated `/api/state` and `/api/widgets`, live normal-server and shared-WM `/wm.js`, live normal-server and shared-WM `/retained_renderer.js`, generated manual evidence, and unit script-helper coverage |
| Browser HTML response CSP, frame, referrer, permissions, cache-control, and anti-sniff headers | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/01_unit/app/ui/async_web_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md` | passing for helper coverage across normal/async/TLS response builders plus live normal root-page and normal/shared-WM `/wm/native_window` evidence; HTML documents are no-store/no-cache with `Expires: 0`; Permissions-Policy now denies hidden powerful APIs including USB, serial, Bluetooth, clipboard, display capture, wake lock, XR, motion sensors, MIDI, autoplay, encrypted media, and fullscreen by default; CSP now includes `object-src 'none'` to disable plugin/object loads, HTML responses include `Origin-Agent-Cluster: ?1` for origin-keyed agent clustering and `Cross-Origin-Embedder-Policy: require-corp` after the browser shell subresource audit found inline scripts, data images, and same-origin script routes with CORP/no-sniff headers; `X-DNS-Prefetch-Control: off` suppresses implicit DNS prefetches, and `X-Permitted-Cross-Domain-Policies: none` denies legacy plugin cross-domain policy discovery |
| Sanitized request-id correlation for token-bearing responses | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| Authorized `/ui/resume` malformed-body rejection and valid-body acceptance | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Authorized `/ui/resume` oversized-body rejection | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| Malformed or ambiguous HTTP request-body framing rejection before body reads | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing for duplicate `Content-Length`, malformed length, unsupported `Transfer-Encoding`, and live normal `/ui/login` duplicate-length evidence |
| Normal, shared-WM, async, and TLS oversized request-head, request-line, and header-line rejection before route dispatch | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing for normal/shared live paths and shared async/TLS predicate coverage |
| Positive token mint plus canonical `/ui/ws` WebSocket upgrade and legacy `/ws` rejection | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 |
| Case-insensitive WebSocket upgrade headers and comma-token `Connection` parsing | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| Inbound WebSocket frame payload length cap before allocation | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` regression run | passing |
| Non-GET WebSocket upgrade rejection for `/ui/ws`, async, and TLS upgrade paths plus legacy route hiding | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-16 for normal/shared live paths and shared async/TLS predicate coverage |
| Normal and shared-WM unknown browser route fallback hardening | `src/app/ui.web/server.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; generated manual `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md` | passing for `/hidden-browser-production-gap` returning JSON `404 not_found` with no-store/no-cache/nosniff headers |
| Warm login plus authenticated WebSocket upgrade latency | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | measured locally with a 10s ceiling |
| Live `/ui/login` fixed-window burst gate | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-17 with explicit per-port `SIMPLE_UI_WEB_ALLOWED_ORIGINS` loopback configuration |
| Live shared-WM `/ui/login` fixed-window burst gate | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passed locally on 2026-06-17 with explicit per-port `SIMPLE_UI_WEB_ALLOWED_ORIGINS` loopback configuration |
| Shared-WM oversized request-head rejection before route dispatch | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| Renderer parity gate | `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` | passing |
| GPU environment matrix | `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`; `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`; `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md` | Linux Vulkan/CUDA/OpenCL pass; Metal/ROCm/DirectX/WebGPU native device-readback still external/partial |

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

## Traceability Matrix

Final `REQ-WEB-HARD-*` and `NFR-WEB-HARD-*` files exist for the selected
Feature Option C and NFR Option C scope. Use this matrix to keep every selected
ID tied to its current evidence artifact.

| Candidate ID | Evidence Artifact | Evidence Status |
|--------------|-------------------|-----------------|
| `REQ-WEB-HARD-001` | `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-002` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `src/app/ui.web/tls_serve_loop.spl` check | passing |
| `REQ-WEB-HARD-003` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-004` | `src/app/ui.web/server.spl`; `src/app/ui.web/ui_routes.spl`; `src/app/ui.web/async_server.spl`; `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-005` | `src/app/ui.web/wm.js`; `test/01_unit/app/ui/ws_handler_spec.spl`; query-token env non-authorization live evidence | passing |
| `REQ-WEB-HARD-006` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-007` | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; generated manual `doc/06_spec/test/03_system/gui/simple_web_browser_production_hardening_spec.md` | passing for canonical `/ui/ws` bearer upgrade and legacy `/ws` route hiding |
| `REQ-WEB-HARD-008` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-009` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `REQ-WEB-HARD-010` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` child-process cleanup path | passing |
| `REQ-WEB-HARD-011` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` normal and shared-WM burst scenarios | passing |
| `REQ-WEB-HARD-012` | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; `src/app/ui.web/auth_params.spl` | passing for deprecated env non-authorization |
| `REQ-WEB-HARD-013` | `scripts/check/check-production-gui-web-renderer-parity-evidence.shs`; `doc/09_report/simple_web_browser_production_hardening.md` | passing locally |
| `REQ-WEB-HARD-014` | `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`; `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`; `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md` | partial: Linux local evidence recorded; Metal/ROCm/DirectX/WebGPU native device-readback requires external hosts |
| `NFR-WEB-HARD-001` | `test/01_unit/app/ui/web_auth_hardening_spec.spl` | passing |
| `NFR-WEB-HARD-002` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; TLS server check | passing |
| `NFR-WEB-HARD-003` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/01_unit/app/ui/async_web_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; JSON, static script, and unknown-route fallback no-store/no-cache/nosniff assertions; HTML CSP/frame/referrer/permissions; sanitized request-id assertions | passing |
| `NFR-WEB-HARD-004` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `NFR-WEB-HARD-005` | `test/01_unit/app/ui/web_auth_hardening_spec.spl`; `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; body/frame/head-size and request-body-framing guards in `src/app/ui.web/server.spl`, `src/app/ui.web/async_server.spl`, `src/app/ui.web/tls_serve_loop.spl`, `src/app/ui.web/ui_routes.spl`, and `src/app/ui.web/auth_params.spl` | passing |
| `NFR-WEB-HARD-006` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` process start/kill helpers | passing |
| `NFR-WEB-HARD-007` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` warm auth latency scenario | measured locally with a 10s ceiling |
| `NFR-WEB-HARD-008` | `test/01_unit/app/ui/ws_handler_spec.spl`; `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`; generated manual | passing |
| `NFR-WEB-HARD-009` | `scripts/check/check-production-gui-web-renderer-parity-evidence.shs` | passing locally |
| `NFR-WEB-HARD-010` | `src/app/ui.web/wm.js`; `test/01_unit/app/ui/ws_handler_spec.spl`; live query-token rejection scenario | passing |
| `NFR-WEB-HARD-011` | `test/03_system/gui/simple_web_browser_production_hardening_spec.spl` | passing |
| `NFR-WEB-HARD-012` | `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`; `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`; `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md` | partial: explicit status rows exist; native Metal/ROCm/DirectX/WebGPU device-readback requires external hosts |

Selected trace IDs are carried by the executable specs and regenerated manuals.

## Release Blockers

- Metal, AMD ROCm, DirectX, and WebGPU native proof require external host
  environments and accepted manifests captured with
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`.
- AC-7 hygiene evidence must be current at handoff; unrelated dirty files and
  existing `jj` conflicts remain separate from this lane.
