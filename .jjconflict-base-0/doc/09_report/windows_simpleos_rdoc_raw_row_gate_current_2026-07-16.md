# Windows SimpleOS RenderDoc Raw Row Gate - 2026-07-16

## Scope

Current Windows refresh for
`scripts/check/check-simpleos-rdoc-raw-row-gate.ps1`.

## Result

- Wrapper path hardening: pass. Evidence directory, Simple binary, aggregate
  script, and summary path now resolve from the checkout root.
- Native stderr handling: pass. The wrapper captures the Rust bootstrap warning
  on stderr without aborting before aggregate row checks.
- Out-of-tree gate: pass from `%TEMP%`.
- Missing RDOC magic case: pass. Missing `simpleos_renderdoc_rdc_magic_status`
  yields `blocked:missing-simple-rdoc-magic` for artifact, WM, and live status.
- Valid RDOC magic case: pass. Explicit `simpleos_renderdoc_rdc_magic_status=pass`
  yields `simpleos_rdoc_raw_row_gate_with_status_live_status=pass`.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-rdoc-raw-row-gate.ps1 -EvidenceDir build\simpleos_multiconfig_live_evidence\rdoc-raw-row-gate-out-of-tree
Pop-Location
```

This protects the release evidence path from raw `RDOC` string rows that omit
the explicit validated magic-status row.
