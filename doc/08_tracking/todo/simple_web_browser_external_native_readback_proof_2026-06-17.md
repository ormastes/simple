# TODO: Simple Web Browser External Native Readback Proof

## Status

Blocked on external host availability.

## Todo

- Run macOS Metal native readback proof.
- Run AMD ROCm/HIP native readback proof.
- Run Windows DirectX native readback proof.
- Run real browser WebGPU `device_readback` proof.
- Capture every result with
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`.
- Update the parent production browser hardening report and feature DB only
  after manifests are accepted by
  `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`
  criteria.

## Local Baseline

Already covered locally before this TODO:

- authenticated `/api/state` and `/api/widgets` `200 OK` JSON responses with
  no-store/no-cache/nosniff headers
- normal/shared-WM `/wm.js` and `/retained_renderer.js` script responses with
  no-store/no-cache/nosniff headers
- shown `/wm/native_window` HTML headers
- hidden unknown-route JSON `404 not_found` fallback headers
- 6-scenario live endpoint pass in
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`

The manifest baseline confirmation rows must be filled before any external gate
can be accepted.

## Parent

- `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16`
- `doc/03_plan/agent_tasks/simple_web_browser_external_native_readback_proof.md`
