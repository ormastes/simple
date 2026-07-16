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
- Desktop-service rebuild bootstrap: advanced past the Windows compiler-loader
  blocker. MSYS2 was repaired with matching mingw64 GCC/LLVM packages plus the
  `riscv64-unknown-elf` GCC/newlib/binutils packages, and the repo now provides
  GCC/G++ wrapper scripts that strip clang-style `--target=riscv64-unknown-elf`
  before delegating to the RISC-V cross tools. Current probe rows show
  `simpleos_qemu_rv64_desktop_service_build_cc_launch_status=pass`,
  `simpleos_qemu_rv64_desktop_service_build_cxx_launch_status=pass`, and empty
  missing-DLL rows. Native-build now reaches the freestanding link and stops at
  `simpleos_qemu_rv64_desktop_service_build_status=blocked:desktop-service-build-exit-1`.
  The retained object-directory diagnostic shows the previous runtime helper
  gaps are resolved; the remaining raw linker diagnostic is duplicate boot
  runtime selection across `baremetal_stubs`, `full_networking_runtime`, and
  `ghdl_boot_info_runtime`. That is now a build graph / boot-source selection
  blocker, not a missing Windows DLL blocker.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-out-of-tree.env
Pop-Location
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-live-current.env -RunLiveBoot -BootTimeoutSeconds 60
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-qemu-rv64-desktop-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\qemu-rv64-desktop-build-toolchain-current.env -BuildDesktopServiceKernel -BuildCc scripts\tool\riscv64-unknown-elf-gcc-wrapper.cmd -BuildCxx scripts\tool\riscv64-unknown-elf-gxx-wrapper.cmd
```

The live command proves the Windows QEMU launch, network probes, QMP screendump,
GPU readback, and WM marker path. RenderDoc `.rdc` and structured QEMU/host
RenderDoc log evidence remain separate gates. The build-toolchain command now
proves the repaired RISC-V compiler launch path and the current RV64
desktop-service link blocker.
