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

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-fpga-rv64-serial-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\fpga-rv64-serial-out-of-tree.env
Pop-Location
```

This does not claim FPGA hardware completion; it hardens and proves the Windows
preflight entrypoint used by the broader SimpleOS multiconfig evidence chain.
