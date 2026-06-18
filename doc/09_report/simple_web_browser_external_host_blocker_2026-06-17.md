# Simple Web Browser External Host Blocker - 2026-06-17

## Scope

This report records the current host capability probe for the remaining Simple
Web browser production hardening release gates described in
`doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md`.

## Probe Command

```sh
date -u +%Y-%m-%dT%H:%M:%SZ
uname -a
command -v xcrun metal metallib rocminfo hipcc powershell pwsh
```

The actual probe also checked `/sys/class/drm`, `/opt/rocm`, and the macOS Metal
framework path.

## Probe Result

- `date_utc=2026-06-17T02:00:02Z`
- `uname=Linux dl 6.8.0-117-generic #117-Ubuntu SMP PREEMPT_DYNAMIC Tue May 5 19:26:24 UTC 2026 x86_64 x86_64 x86_64 GNU/Linux`
- `os=Linux`
- `xcrun=missing`
- `metal=missing`
- `metallib=missing`
- `rocminfo=missing`
- `hipcc=missing`
- `powershell=missing`
- `pwsh=missing`
- `opt_rocm=missing`
- `metal_framework=missing`
- DRM cards are visible under `/sys/class/drm`, but no ROCm/HIP toolchain is
  installed on this host.

## Current Session Probe Refresh

The current session rechecked the remaining native proof prerequisites:

- `date_utc=2026-06-17T10:21:08Z`
- `host_system=Linux`
- `host_release=6.8.0-117-generic`
- `host_machine=x86_64`
- `xcrun=missing`
- `metal=missing`
- `metallib=missing`
- `rocminfo=missing`
- `hipcc=missing`
- `powershell=missing`
- `pwsh=missing`
- `opt_rocm=missing`
- `metal_framework=missing`
- `drm_cards=card1,card1-DP-1,card1-DP-2,card1-DP-3,card1-DP-4,card2,card2-DP-5,card2-DP-6,card2-DP-7,card2-HDMI-A-1,card2-Unknown-2,renderD128,renderD129,version`

## Crashed Rollout Audit

The crashed rollout named by the handoff was inspected before continuing:

- `rollout=/home/ormastes/.codex/sessions/2026/06/02/rollout-2026-06-02T01-05-12-019e85dc-fb0c-73b0-b0c6-2a6ead9624ed.jsonl`
- `cwd=/home/ormastes/dev/pub/simple`
- `separate_worktree=none found`
- `task_scope=modern_wm_readiness / Simple WM modernization`
- `relevant_external_native_readback_manifest=none found`

The rollout did not leave usable macOS Metal, ROCm/HIP, Windows DirectX, or real
browser WebGPU `device_readback` evidence for this follow-up. Its work is not
accepted as external proof for this production-hardening gate.

## Gate Status

| Gate | Current Host Result | Reason |
| --- | --- | --- |
| macOS Metal native readback | blocked on external host | Current host is Linux and lacks `xcrun`, `metal`, `metallib`, and `Metal.framework`. |
| AMD ROCm/HIP native readback | blocked on external host/toolchain | Current host lacks `rocminfo`, `hipcc`, and `/opt/rocm`. |
| Windows DirectX native readback | blocked on external host | Current host is Linux and lacks PowerShell/Windows DirectX runtime proof. |
| Browser WebGPU real device readback | still open | Must be run on a browser/runtime stack that reports `webgpu_real_readback_source=device_readback`. |

## Current Local Baseline

Before handing off to external hosts, the local Linux lane has passing browser
hardening evidence for:

- authenticated `/api/state` and `/api/widgets` `200 OK` JSON responses with
  no-store/no-cache/nosniff headers
- normal/shared-WM `/wm.js` and `/retained_renderer.js` script responses with
  no-store/no-cache/nosniff headers
- shown `/wm/native_window` HTML response headers
- hidden unknown-route JSON `404 not_found` fallback headers
- 6-scenario live endpoint pass in
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`

## Next Required Evidence

Run the exact commands in
`doc/03_plan/sys_test/simple_web_browser_external_host_proof_runbook.md` on the
required macOS, AMD ROCm/HIP, Windows DirectX, and WebGPU-capable hosts, and
capture each result with
`doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`.
The parent production hardening feature can only close after those manifests
are accepted by the runbook criteria, including baseline confirmation rows.
This report is blocker evidence only; it does not close `REQ-WEB-HARD-014` or
`NFR-WEB-HARD-012`.
