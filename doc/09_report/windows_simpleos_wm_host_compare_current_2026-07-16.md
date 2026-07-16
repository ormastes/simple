# Windows SimpleOS WM Host Compare Evidence - 2026-07-16

## Scope

Current Windows refresh for `scripts/check/check-simpleos-wm-host-compare-evidence.ps1`.

## Result

- Wrapper path hardening: pass. Repo-relative evidence, PPM, log, Simple binary,
  and capture entry paths resolve from the checkout root even when the script is
  launched from `%TEMP%`.
- Hosted WM capture: pass. `simpleos_host_wm_capture_status=pass`,
  `simpleos_host_wm_capture_exit_code=0`.
- QEMU PPM evidence: pass. `simpleos_wm_qemu_ppm_status=pass`, `320x240`,
  `simpleos_wm_qemu_capture_kind=qemu-wm-rect-scene`.
- Host PPM evidence: pass. `simpleos_wm_host_ppm_status=pass`, `320x240`,
  `simpleos_wm_host_capture_kind=hosted-wm-rect-scene`.
- Strict ARGB comparison: pass. `simpleos_wm_argb_diff_status=pass`,
  `simpleos_wm_argb_mismatch_count=0`.
- Fresh live-QEMU source: pass. After the desktop-service QEMU live boot, the
  wrapper compared the fresh `qemu-screendump.ppm` against a hosted WM capture
  and again reported `simpleos_wm_argb_diff_status=pass` with
  `simpleos_wm_argb_mismatch_count=0`.
- Release compare gate: missing. `simpleos_wm_qemu_host_compare_status=missing`
  because QEMU/host RenderDoc logs and `simpleos-wm.rdc` are not present.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-wm-host-compare-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\wm-host-compare-out-of-tree-capture.env -HostPpmPath build\os\systest\qemu-riscv64-desktop\host-wm-out-of-tree.ppm -HostCaptureLogPath build\simpleos_multiconfig_live_evidence\host-wm-capture-out-of-tree.log -AttemptHostWmCapture
Pop-Location
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-wm-host-compare-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\wm-host-compare-live-current.env -AttemptHostWmCapture
```

The command exits fail-closed because the RenderDoc artifacts are missing, but
the host capture and zero-mismatch PPM comparison rows pass.
