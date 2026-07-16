# GUI Web/2D DirectX Windows Current Evidence - 2026-07-16

Current Windows PowerShell run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --check -BuildDir build\gui-web-2d-directx-env-windows-current-check -EvidencePath build\gui-web-2d-directx-env-windows-current-check\evidence.env -TimeoutSecs 90
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --browser-backing -BuildDir build\gui-web-2d-directx-env-windows-current-browser -EvidencePath build\gui-web-2d-directx-env-windows-current-browser\evidence.env -TimeoutSecs 120
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --gpu-capture -BuildDir build\gui-web-2d-directx-env-windows-current-gpucap -EvidencePath build\gui-web-2d-directx-env-windows-current-gpucap\evidence.env -TimeoutSecs 160
```

Result:

- `gui_web_2d_directx_native_readback_status=pass`
- `gui_web_2d_directx_native_readback_reason=directx-native-d3d11-staging-readback-matched`
- `gui_web_2d_directx_native_readback_source=device_readback`
- `gui_web_2d_directx_native_readback_expected_checksum=1023148974`
- `gui_web_2d_directx_native_readback_actual_checksum=1023148974`
- `gui_web_2d_directx_electron_browser_backing_status=pass`
- `gui_web_2d_directx_electron_browser_backing_d3d11_hint_present=true`
- `gui_web_2d_directx_electron_browser_backing_gpu_compositing=enabled`
- `gui_web_2d_directx_electron_browser_backing_webgl=enabled`
- `gui_web_2d_directx_chrome_browser_backing_status=pass`
- `gui_web_2d_directx_chrome_browser_backing_d3d11_hint_present=true`
- `gui_web_2d_directx_browser_backing_status=pass`
- `gui_web_2d_directx_browser_backing_reason=native-d3d11-electron-chrome-pass`
- `gui_web_2d_directx_gpu_debugger_tool=DXCap.exe`
- `gui_web_2d_directx_gpu_debugger_capture_status=pass`
- `gui_web_2d_directx_gpu_debugger_capture_reason=vsglog-gfxa-magic-pass`
- `gui_web_2d_directx_gpu_debugger_capture_artifact_magic=GFXA`

Primary artifacts:

- `build/gui-web-2d-directx-env-windows-current-check/evidence.env`
- `build/gui-web-2d-directx-env-windows-current-browser/evidence.env`
- `build/gui-web-2d-directx-env-windows-current-gpucap/evidence.env`
- `build/gui-web-2d-directx-env-windows-current-gpucap/dxcap_chrome_d3d11.vsglog`
- `build/gui-web-2d-directx-env-windows-current-gpucap/dxcap_chrome_d3d11.png`

