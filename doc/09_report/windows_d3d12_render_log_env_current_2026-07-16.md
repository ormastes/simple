# Windows D3D12 Render Log Environment - 2026-07-16

Current Windows PowerShell run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-windows-d3d12-render-log-env.ps1 --refresh-directx -BuildDir build\windows-d3d12-render-log-env-current -TimeoutSecs 160
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-windows-d3d12-render-log-env.ps1 --refresh-directx -BuildDir build\windows-d3d12-render-log-env-strict-current -TimeoutSecs 160
```

Result:

- `windows_d3d12_render_log_compare_status=fail`
- `windows_d3d12_render_log_compare_blocked_gate_count=5`
- `windows_d3d12_render_log_compare_blocked_gates=windows-d3d12-native-readback,browser-d3d12-backing,pairwise-argb-diff,argb-source-evidence,pix-or-gpu-debugger`
- `windows_d3d12_render_log_compare_directx_diagnostic_env_file_status=pass`
- `windows_d3d12_render_log_compare_directx_diagnostic_status=pass`
- `windows_d3d12_render_log_compare_directx_diagnostic_event_status=pass`
- `windows_d3d12_render_log_compare_directx_diagnostic_gpu_capture_status=pass`
- `windows_d3d12_render_log_compare_directx_strict_diagnostic_status=pass`
- `windows_d3d12_render_log_compare_directx_diagnostic_api=d3d11`
- `windows_d3d12_render_log_compare_refresh_directx_exit_code=0`
- `windows_d3d12_pix_capture_status=unavailable`
- `windows_d3d12_pix_capture_tool=`
- `windows_d3d12_gpu_debugger_capture_tool=C:\WINDOWS\system32\DXCap.exe`
- `windows_d3d12_gpu_debugger_directx_diagnostic_status=pass`

The wrapper now runs on Windows PowerShell without throwing on
`ProcessStartInfo.ArgumentList`, refreshes the DirectX diagnostic evidence, and
fails closed on the D3D12-specific gates. D3D11/DXCap evidence is intentionally
not promoted to D3D12 completion evidence.

Environment bootstrap attempt:

```powershell
winget install --id Microsoft.PIX --accept-source-agreements --accept-package-agreements --silent
```

The PIX installer started but remained at the elevated engine phase. The log
ended at `Launching elevated engine process.` `Microsoft.PIX` was not listed as
installed afterward, and no `WinPix.exe` was discoverable. Non-elevated cleanup
stopped the winget and PIX bootstrapper processes, but one elevated `msiexec`
child could not be terminated from this shell (`Access is denied`).

Primary artifacts:

- `build/windows-d3d12-render-log-env-current/evidence.env`
- `build/windows-d3d12-render-log-env-current/windows-d3d12-native-readback.env`
- `build/windows-d3d12-render-log-env-current/windows-d3d12-browser-backing.env`
- `build/windows-d3d12-render-log-env-current/windows-d3d12-pix.env`
- `build/windows-d3d12-render-log-env-current/directx-diagnostic/evidence.env`
- `build/windows-d3d12-render-log-env-current/report.md`
- `build/windows-d3d12-render-log-env-strict-current/evidence.env`
- `build/windows-d3d12-render-log-env-strict-current/directx-diagnostic/evidence.env`

Code change:

- `scripts/setup/setup-windows-d3d12-render-log-env.ps1` now uses
  PowerShell-compatible process argument quoting and discovers PIX through
  `WinPix.exe`, legacy `PIXWin.exe`, and versioned `Program Files\Microsoft PIX`
  install paths.
- The wrapper now records strict upstream DirectX diagnostic status. The strict
  status is `pass` only when DirectX browser backing, browser event routing, and
  DXCap GPU capture all pass; stale DirectX evidence without event proof no
  longer looks equivalent in D3D12 reports.
