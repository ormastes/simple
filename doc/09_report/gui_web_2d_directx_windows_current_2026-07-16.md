# GUI Web/2D DirectX Windows Current Evidence - 2026-07-16

Current Windows PowerShell run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --check -BuildDir build\gui-web-2d-directx-env-windows-current-check -EvidencePath build\gui-web-2d-directx-env-windows-current-check\evidence.env -TimeoutSecs 90
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --browser-backing -BuildDir build\gui-web-2d-directx-env-windows-current-browser -EvidencePath build\gui-web-2d-directx-env-windows-current-browser\evidence.env -TimeoutSecs 120
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --gpu-capture -BuildDir build\gui-web-2d-directx-env-windows-current-gpucap -EvidencePath build\gui-web-2d-directx-env-windows-current-gpucap\evidence.env -TimeoutSecs 160
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --gpu-capture -BuildDir build\gui-web-2d-directx-env-windows-event-gpucap -EvidencePath build\gui-web-2d-directx-env-windows-event-gpucap\evidence.env -TimeoutSecs 160
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-directx-env.ps1 --gpu-capture -BuildDir build\gui-web-2d-directx-env-windows-event-strict-gpucap -EvidencePath build\gui-web-2d-directx-env-windows-event-strict-gpucap\evidence.env -TimeoutSecs 160
powershell -ExecutionPolicy Bypass -File scripts\check\check-gui-web-2d-directx-strict-evidence.ps1 -EvidencePath build\gui-web-2d-directx-env-windows-event-strict-gpucap\evidence.env -RequireGpuCapture
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\setup\setup-gui-web-2d-directx-env.ps1 --check -BuildDir build\gui-web-2d-directx-env-out-of-tree-check
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
- `gui_web_2d_directx_browser_event_status=pass`
- `gui_web_2d_directx_browser_event_reason=electron-chrome-events-pass`
- `gui_web_2d_directx_electron_event_status=pass`
- `gui_web_2d_directx_electron_argb_width=1280`
- `gui_web_2d_directx_electron_argb_height=720`
- `gui_web_2d_directx_electron_argb_pixel_count=921600`
- `gui_web_2d_directx_electron_argb_nonblank_pixel_count=921600`
- `gui_web_2d_directx_electron_focus_event_count=3`
- `gui_web_2d_directx_electron_keyboard_event_count=2`
- `gui_web_2d_directx_electron_input_event_count=1`
- `gui_web_2d_directx_electron_pointer_down_event_count=2`
- `gui_web_2d_directx_electron_pointer_up_event_count=2`
- `gui_web_2d_directx_electron_click_event_count=1`
- `gui_web_2d_directx_chrome_event_status=pass`
- `gui_web_2d_directx_chrome_argb_width=1280`
- `gui_web_2d_directx_chrome_argb_height=720`
- `gui_web_2d_directx_chrome_argb_pixel_count=921600`
- `gui_web_2d_directx_chrome_argb_nonblank_pixel_count=921600`
- `gui_web_2d_directx_chrome_focus_event_count=2`
- `gui_web_2d_directx_chrome_keyboard_event_count=2`
- `gui_web_2d_directx_chrome_input_event_count=1`
- `gui_web_2d_directx_chrome_pointer_down_event_count=2`
- `gui_web_2d_directx_chrome_pointer_up_event_count=2`
- `gui_web_2d_directx_chrome_click_event_count=1`
- `gui_web_2d_directx_gpu_debugger_tool=DXCap.exe`
- `gui_web_2d_directx_gpu_debugger_capture_status=pass`
- `gui_web_2d_directx_gpu_debugger_capture_reason=vsglog-gfxa-magic-pass`
- `gui_web_2d_directx_gpu_debugger_capture_artifact_magic=GFXA`
- `gui_web_2d_directx_strict_evidence_status=pass`
- `gui_web_2d_directx_strict_evidence_reason=pass`
- `gui_web_2d_directx_strict_evidence_argb_metrics_status=pass`
- `gui_web_2d_directx_strict_evidence_gpu_capture_artifact_magic=GFXA`

Primary artifacts:

- `build/gui-web-2d-directx-env-windows-current-check/evidence.env`
- `build/gui-web-2d-directx-env-windows-current-browser/evidence.env`
- `build/gui-web-2d-directx-env-windows-current-gpucap/evidence.env`
- `build/gui-web-2d-directx-env-windows-current-gpucap/dxcap_chrome_d3d11.vsglog`
- `build/gui-web-2d-directx-env-windows-current-gpucap/dxcap_chrome_d3d11.png`
- `build/gui-web-2d-directx-env-windows-event-gpucap/evidence.env`
- `build/gui-web-2d-directx-env-windows-event-gpucap/electron_argb_proof.json`
- `build/gui-web-2d-directx-env-windows-event-gpucap/chrome_argb_proof.json`
- `build/gui-web-2d-directx-env-windows-event-gpucap/dxcap_chrome_d3d11.vsglog`
- `build/gui-web-2d-directx-env-windows-event-gpucap/dxcap_chrome_d3d11.png`
- `build/gui-web-2d-directx-env-windows-event-strict-gpucap/evidence.env`
- `build/gui-web-2d-directx-env-windows-event-strict-gpucap/electron_argb_proof.json`
- `build/gui-web-2d-directx-env-windows-event-strict-gpucap/chrome_argb_proof.json`
- `build/gui-web-2d-directx-env-windows-event-strict-gpucap/dxcap_chrome_d3d11.vsglog`
- `scripts/check/check-gui-web-2d-directx-strict-evidence.ps1`

The event-enabled capture records focus, keyboard, text input, pointer down/up,
and click delivery in both Electron and Chrome before the ARGB readback and
DXCap GPU-debugger capture. This evidence is stronger than static screenshot or
pixel proof alone. The strict wrapper gate now requires
`gui_web_2d_directx_browser_event_status=pass` for `--browser-backing` and
`--gpu-capture`; browser pixels and GPU backing are not sufficient without
event-routing evidence.

The strict evidence checker validates existing env files without rerunning live
capture. It now requires Electron and Chrome ARGB source metrics to be present,
nonzero, and dimension-consistent with the requested capture size. It passes on
the strict artifact above and fails closed on older artifacts that predate
browser event proof rows or ARGB source metrics.

The DirectX setup wrapper now runs child processes from the repository root.
The out-of-tree `--check` command above was launched from
`C:\Users\ormas\AppData\Local\Temp` by absolute script path and still executed
the native D3D11 readback probe, reporting
`gui_web_2d_directx_native_readback_status=pass`,
`gui_web_2d_directx_native_readback_expected_checksum=1023148974`, and
`gui_web_2d_directx_native_readback_actual_checksum=1023148974`.
