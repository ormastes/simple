# GUI Web/2D Vulkan Windows Current Evidence - 2026-07-16

Current Windows PowerShell run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-gui-web-2d-vulkan-env.ps1 --check -BuildDir build\gui-web-2d-vulkan-env-windows-current-check -EvidencePath build\gui-web-2d-vulkan-env-windows-current-check\evidence.env -TimeoutSecs 90
powershell -ExecutionPolicy Bypass -File scripts\check\check-gui-web-2d-vulkan-strict-evidence.ps1 -EvidencePath build\gui-web-2d-vulkan-env-windows-current-check\evidence.env
powershell -ExecutionPolicy Bypass -File scripts\check\check-gui-web-2d-vulkan-strict-evidence.ps1 -EvidencePath build\gui-web-2d-vulkan-env-windows-current-check\evidence.env -RequireHostReadiness
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\setup\setup-gui-web-2d-vulkan-env.ps1 --check -BuildDir build\gui-web-2d-vulkan-env-out-of-tree-check
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-gui-web-2d-vulkan-strict-evidence.ps1 -EvidencePath build\gui-web-2d-vulkan-env-out-of-tree-check\evidence.env
```

Result:

- `gui_web_2d_vulkan_simple_status=pass`
- `gui_web_2d_vulkan_simple_backend_name=vulkan`
- `gui_web_2d_vulkan_simple_argb_width=16`
- `gui_web_2d_vulkan_simple_argb_height=16`
- `gui_web_2d_vulkan_simple_argb_pixel_count=256`
- `gui_web_2d_vulkan_simple_argb_checksum=140781974135910`
- `gui_web_2d_vulkan_vulkaninfo_status=pass`
- `gui_web_2d_vulkan_vulkaninfo_path=C:\WINDOWS\system32\vulkaninfo.exe`
- `gui_web_2d_vulkan_dxc_status=pass`
- `gui_web_2d_vulkan_dxc_path=C:\Program Files (x86)\Windows Kits\10\bin\10.0.26100.0\x64\dxc.exe`
- `gui_web_2d_vulkan_glslang_validator_status=missing`
- `gui_web_2d_vulkan_spirv_as_status=missing`
- `gui_web_2d_vulkan_renderdoc_status=missing`
- `gui_web_2d_vulkan_sdk_tools_status=blocked:sdk-tools-missing`
- `gui_web_2d_vulkan_host_readiness_status=blocked:sdk-tools-missing`
- Partial checker: `gui_web_2d_vulkan_strict_evidence_status=pass`
- Partial checker: `gui_web_2d_vulkan_strict_evidence_reason=pass`
- Partial checker: `gui_web_2d_vulkan_strict_evidence_simple_metrics_status=pass`
- Host-readiness checker: `gui_web_2d_vulkan_strict_evidence_status=fail`
- Host-readiness checker: `gui_web_2d_vulkan_strict_evidence_reason=sdk-tools,renderdoc-tools,host-readiness`

Environment bootstrap attempt:

```powershell
winget install --id KhronosGroup.VulkanSDK --accept-source-agreements --accept-package-agreements --silent
```

The Vulkan SDK installer reached the administrator/UAC step and returned
`0x800704c7 : The operation was canceled by the user.` RenderDoc is also not
installed (`BaldurKarlsson.RenderDoc` is available through winget but was not
installed after the SDK UAC cancellation).

Primary artifacts:

- `build/gui-web-2d-vulkan-env-windows-current-check/evidence.env`
- `scripts/setup/setup-gui-web-2d-vulkan-env.ps1`
- `scripts/check/check-gui-web-2d-vulkan-strict-evidence.ps1`

Code change:

- The Vulkan setup wrapper now discovers `dxc.exe` from the installed Windows
  Kit when Vulkan SDK `Bin\dxc.exe` is absent. This prevents a false `dxc`
  missing result on Windows hosts with the DirectX shader compiler installed
  through the Windows SDK.
- The Vulkan strict evidence checker validates saved env files without rerunning
  live capture. Its default mode accepts the partial evidence currently present
  on this host only when the saved Simple Vulkan readback metrics are present
  and positive: `16x16`, 256 pixels, backend `vulkan`, and checksum
  `140781974135910`; `-RequireHostReadiness` fails closed until
  `glslangValidator`, `spirv-as`, and RenderDoc are installed.
- The Vulkan setup wrapper now resolves the default Simple readback evidence
  path from the repository root and runs child processes from the repository
  root. The out-of-tree `--check` command above was launched from
  `C:\Users\ormas\AppData\Local\Temp` by absolute script path and still
  reported `gui_web_2d_vulkan_simple_status=pass`,
  `gui_web_2d_vulkan_simple_backend_name=vulkan`,
  `gui_web_2d_vulkan_vulkaninfo_status=pass`, and
  `gui_web_2d_vulkan_dxc_status=pass`; the generated env passed the default
  strict checker.
