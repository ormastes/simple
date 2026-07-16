# Windows SimpleOS QEMU RV64 Desktop Evidence - 2026-07-16

## Scope

Current Windows refresh for
`scripts/check/check-simpleos-qemu-rv64-desktop-evidence.ps1`.

## Result

- Wrapper path hardening: pass. The direct QEMU RV64 desktop wrapper now anchors
  itself to the checkout root and resolves repo-owned evidence, artifact,
  kernel, disk image, Simple binary, desktop-service, disk-image-builder, and
  log paths from there.
- Out-of-tree preflight: pass as a fail-closed evidence run from `%TEMP%`.
- QEMU binary discovery: pass. The wrapper found
  `C:\dev\tool\msys2\mingw64\bin\qemu-system-riscv64.exe`.
- Kernel preflight: pass. `simpleos_qemu_rv64_kernel_status=pass` and
  `simpleos_qemu_rv64_canonical_kernel_status=pass`.
- Disk image preflight: pass. `simpleos_qemu_rv64_image_status=pass` and
  `simpleos_qemu_rv64_canonical_image_status=pass`.
- Live boot/capture: pass. `-RunLiveBoot` now selects the existing desktop
  service kernel when available and reports
  `simpleos_qemu_rv64_live_kernel_selection=existing-desktop-service`.
  The Windows run launches QEMU, captures serial output, SSH, HTTP, QMP
  screendump, GPU readback, and the WM marker:
  `simpleos_qemu_serial_console_status=pass`,
  `simpleos_qemu_rv64_ssh_probe_status=pass`,
  `simpleos_qemu_rv64_http_probe_status=pass`,
  `simpleos_qemu_rv64_http_status_code=200`,
  `simpleos_qemu_rv64_qmp_status=pass`,
  `simpleos_qemu_gpu_readback_status=pass`,
  `simpleos_qemu_wm_marker_status=pass`, and
  `simpleos_qemu_rv64_blocker=pass`.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-out-of-tree.env
Pop-Location
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-live-current.env -RunLiveBoot -BootTimeoutSeconds 60
```

The live command proves the Windows QEMU launch, network probes, QMP screendump,
GPU readback, and WM marker path. RenderDoc `.rdc` and structured QEMU/host
RenderDoc log evidence remain separate gates.
