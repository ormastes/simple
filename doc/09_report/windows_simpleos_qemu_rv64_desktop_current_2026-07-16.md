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
- Live boot serial: pass. `-RunLiveBoot` launches QEMU, captures OpenSBI and
  SimpleOS serial output, and reports `simpleos_qemu_serial_console_status=pass`
  after `SIMPLEOS_RISCV_SMF_FS_PASS` / `TEST PASSED`.
- Live service/capture probes: fail closed. The guest exits after the serial
  pass before SSH, HTTP, QMP screendump, or structured WM/GPU readback can be
  probed, so the current evidence reports
  `simpleos_qemu_rv64_live_boot_status=guest-exited-before-service-probes`,
  `simpleos_qemu_rv64_qemu_exit_status=exited:unknown`, and
  `simpleos_qemu_rv64_blocker=guest-exited-before-service-probes`.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-out-of-tree.env
Pop-Location
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-live-current.env -RunLiveBoot -BootTimeoutSeconds 60
```

The live command proves the Windows QEMU launch and serial boot path, but it
does not complete the release capture gate because the guest exits before
network and GPU/WM capture probes.
