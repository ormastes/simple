# Simple Web Browser External Host Evidence Manifest Template

Use this template for each external native rendering proof run referenced by
`doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`.

## Run Identity

- Gate:
- Host OS:
- Host architecture:
- GPU model:
- Driver/runtime version:
- Repo revision:
- Date:

## Local Baseline Confirmation

Confirm the external host checkout includes the 2026-06-17 local browser
hardening baseline before recording a gate pass:

| Baseline Item | Confirmed | Evidence |
| --- | --- | --- |
| Authenticated `/api/state` `200 OK` JSON response has no-store/no-cache/nosniff headers |  |  |
| Authenticated `/api/widgets` `200 OK` JSON response has no-store/no-cache/nosniff headers |  |  |
| Normal/shared-WM `/wm.js` and `/retained_renderer.js` script responses have no-store/no-cache/nosniff headers |  |  |
| Shown `/wm/native_window` HTML response headers are hardened |  |  |
| Hidden unknown-route JSON `404 not_found` fallback headers are hardened |  |  |
| Focused live endpoint suite passes 6 scenarios |  |  |

Do not mark the external gate accepted if any baseline row is unconfirmed.

## Commands

| Command | Exit Status | Report Path | Evidence Env Path |
| --- | --- | --- | --- |
|  |  |  |  |

## Required Fields

Machine-readable fields below are mandatory. Keep one `key=value` per line so
the local acceptance checker can validate the manifest before the feature is
closed:

```text
simple_web_browser_external_host_manifest_status=pass
simple_web_browser_external_host_gate=<metal|rocm|directx|webgpu>
simple_web_browser_external_host_accepted=yes
simple_web_browser_external_host_baseline_confirmed=yes
host_os=
gpu_model=
driver_runtime_version=
command_exit_status=0
report_path=
expected_checksum=
actual_checksum=
mismatch_count=0
```

| Field | Value |
| --- | --- |
| Status field |  |
| Readback source |  |
| Device/backend handle |  |
| Expected checksum |  |
| Actual checksum |  |
| Mismatch count |  |

## Per-Gate Field Checklist

Fill the row matching the gate under test and leave non-applicable rows blank.

| Gate | Required Fields |
| --- | --- |
| macOS Metal | `metal_generated_2d_readback_status=pass`; `metal_engine2d_framebuffer_readback_status=pass`; native Metal device evidence present; no `metal-requires-macos`, `host-unavailable`, or `not_device_readback` rows |
| AMD ROCm/HIP | `rocm_generated_2d_readback_status=pass`; ROCm/HIP device submit/readback evidence present; aggregate queue no longer reports ROCm as unavailable or non-device readback |
| Windows DirectX | `directx_native_readback_status=pass`; positive backend/device handle; readback source `device_readback`; expected/actual checksums match |
| Browser WebGPU | `webgpu_real_readback_status=pass`; `webgpu_real_readback_source=device_readback`; `webgpu_real_readback_backend_handle` positive; expected/actual checksums match |

Before accepting a filled manifest, run:

```sh
sh scripts/check/check-simple-web-browser-external-host-evidence-manifest.shs <manifest.md>
```

## Gate Verdict

- Verdict: pass/fail/unavailable
- Accepted by runbook criteria: yes/no
- Notes:
