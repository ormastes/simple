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
- Live boot/capture: not run in this evidence slice. The wrapper exits
  fail-closed with `simpleos_qemu_rv64_blocker=live-boot-not-run-by-preflight`.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-out-of-tree.env
Pop-Location
```

This does not replace the live QEMU boot/capture gate; it hardens and proves the
direct Windows preflight entrypoint used by the broader live evidence chain.
