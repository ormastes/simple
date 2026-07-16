# Windows SimpleOS FPGA RV64 Serial Evidence - 2026-07-16

## Scope

Current Windows refresh for
`scripts/check/check-simpleos-fpga-rv64-serial-evidence.ps1`.

## Result

- Wrapper path hardening: pass. The direct FPGA RV64 serial wrapper now anchors
  itself to the checkout root and resolves repo-owned evidence, base evidence,
  expected entry, expected kernel, Simple binary, build log, serial log, and
  serial inventory paths from there.
- Out-of-tree preflight: pass as a fail-closed evidence run from `%TEMP%`.
- Expected entry: pass. `simpleos_fpga_expected_entry_status=pass`.
- Expected kernel: pass. `simpleos_fpga_expected_kernel_status=pass`.
- Serial hardware/capture: missing. `simpleos_fpga_serial_device_status=missing`,
  `simpleos_fpga_serial_boot_marker_status=missing`.
- Toolchain/bitstream: missing. `simpleos_fpga_toolchain_status=missing`,
  `simpleos_fpga_bitstream_status=missing`.
- FPGA kernel rebuild bootstrap: blocked with explicit compiler diagnostics.
  The wrapper now accepts and records `-BuildCxx` in addition to `-BuildCc`,
  probes both compilers before native-build, and reports
  `simpleos_fpga_build_status=blocked:build-cc-launch-failed` on the current
  Windows MSYS2 LLVM install. Current rows show
  `simpleos_fpga_build_cc_launch_exit_code=-1073741515` and
  `simpleos_fpga_build_cxx_launch_exit_code=-1073741515`. `objdump -p` shows
  the installed `clang++.exe` imports `libLLVM-19.dll`, which is absent from
  `C:\dev\tool\msys2`; this is the local RV64 rebuild blocker before any FPGA
  hardware/bitstream gate.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\fpga-rv64-serial-out-of-tree.env
Pop-Location
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\fpga-rv64-serial-build-toolchain-current.env -BuildFpgaSerialKernel -BuildCc C:\dev\tool\msys2\mingw64\bin\clang.exe -BuildCxx C:\dev\tool\msys2\mingw64\bin\clang++.exe
```

This does not claim FPGA hardware completion; it hardens and proves the Windows
preflight and rebuild-bootstrap entrypoints used by the broader SimpleOS
multiconfig evidence chain.
