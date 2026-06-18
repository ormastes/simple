# Simple Web Browser External Native Readback Proof Plan

Feature ID: `SIMPLE_WEB_BROWSER_EXTERNAL_NATIVE_READBACK_PROOF_2026_06_17`

## Scope

This follow-up exists because the current Linux host cannot complete the
remaining production browser rendering gates for:

- macOS Metal native readback.
- AMD ROCm/HIP native readback.
- Windows DirectX native readback.
- Real browser WebGPU `device_readback`.

The parent production hardening lane remains `current` until these external
proofs pass or the selected requirements are explicitly re-scoped.

## Inputs

- Runbook: `doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`
- Matrix: `doc/03_plan/sys_test/simple_web_browser_gpu_environment_matrix.md`
- Manifest template:
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`
- Current-host blocker:
  `doc/09_report/simple_web_browser_external_host_blocker_2026-06-17.md`

## Current Local Baseline

The external runs start from a local Linux browser-hardening baseline where the
focused live endpoint suite already passes 6 scenarios. Local PASS evidence
includes:

- authenticated `/api/state` and `/api/widgets` `200 OK` JSON responses with
  no-store/no-cache/nosniff headers
- normal/shared-WM `/wm.js` and `/retained_renderer.js` script responses with
  no-store/no-cache/nosniff headers
- shown `/wm/native_window` HTML response headers
- hidden unknown-route JSON `404 not_found` fallback headers

Do not rerun local convergence work on external hosts unless the runbook changes
or an external proof exposes a regression; the open scope is native device
readback evidence.

## Current Session Direction

This Linux environment cannot produce the remaining Metal, ROCm/HIP, DirectX, or
real browser WebGPU `device_readback` proof. Treat that as an environmental
blocker, not an implementation failure.

Continue the lane from the existing feature and TODO requests:

- Feature:
  `doc/08_tracking/feature/simple_web_browser_external_native_readback_proof_2026-06-17.md`
- TODO:
  `doc/08_tracking/todo/simple_web_browser_external_native_readback_proof_2026-06-17.md`

Next productive work is to run the external-host runbook on capable machines and
attach completed evidence manifests. Local code/spec/doc convergence should only
resume if one of those manifests exposes a regression.

## Work Items

1. Run the Metal commands from the runbook on macOS with Xcode command line
   tools and an available `MTLDevice`.
2. Run the ROCm/HIP commands from the runbook on a supported AMD GPU host with
   `rocminfo`, `hipcc`, and matching `HIP_ARCH`.
3. Run the DirectX native readback commands from the runbook on a native Windows
   DirectX host.
4. Run the real browser WebGPU readback commands from the runbook on a browser
   stack that can report `webgpu_real_readback_source=device_readback`.
5. For each host, fill one copy of the manifest template with command status,
   report paths, device/backend handles, readback source, and checksum fields.
6. Only after all accepted manifests exist, update the GPU matrix, production
   hardening report, local completion audit, and feature DB status.

## Stop Conditions

- Success: all four external manifests satisfy the runbook acceptance fields.
- Blocked: a required host/toolchain remains unavailable; update the blocker
  report and keep the parent feature `current`.
