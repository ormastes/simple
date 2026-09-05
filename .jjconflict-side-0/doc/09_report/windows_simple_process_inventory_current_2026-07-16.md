# Windows Simple Process Inventory Evidence - 2026-07-16

## Scope

Current Windows refresh for `scripts/check/check-simple-process-inventory.ps1`.

## Result

- Wrapper path hardening: pass. The helper now resolves repo-relative evidence
  paths from the checkout root, matching the SimpleOS multiconfig wrapper that
  calls it.
- Out-of-tree preflight: pass from `%TEMP%`.
- Process inventory: pass. `simple_process_inventory_status=pass`,
  `simple_process_inventory_count=0`,
  `simple_process_inventory_over_limit=false`.
- Process cleanup: not requested. `simple_process_inventory_kill_requested=false`.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simple-process-inventory.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\simple-process-inventory-out-of-tree.env -ProcessLimit 100000 -MaxSample 5
Pop-Location
```

This supports the Windows SimpleOS multiconfig evidence path by making stale
`simple.exe` process checks deterministic from any caller working directory.
