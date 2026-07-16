# Windows SimpleOS Engine2D RenderDoc Evidence - 2026-07-16

## Scope

Current Windows refresh for
`scripts/check/check-simpleos-engine2d-renderdoc-evidence.ps1`.

## Result

- Wrapper path hardening: pass. Repo-relative evidence, source evidence, QEMU
  readback, RenderDoc artifact, log, Simple binary, and nested Simple Vulkan
  probe paths resolve from the checkout root even when launched from `%TEMP%`.
- Source evidence discovery: pass. The wrapper finds
  `build/gui-web-2d-vulkan-env/evidence.env` by repo-root path.
- SimpleOS/QEMU readback: pass. `simpleos_qemu_gpu_readback_status=pass`,
  `simpleos_qemu_gpu_readback_width=320`,
  `simpleos_qemu_gpu_readback_height=240`.
- Source bridge audit: pass. The RV64 desktop-service entry now imports
  `create_fb_engine_core`, draws the WM scene through the Simple
  `Engine2DBaremetalCore`, and flushes through the RISC-V `rt_gui_fill4` /
  `rt_gui_flush` runtime shim. The refreshed evidence reports
  `simpleos_engine2d_source_current_draw_path=freestanding-engine2d-baremetal-core`
  and `simpleos_engine2d_source_bridge_audit_status=pass`.
- Engine2D readback promotion: pass for the saved direct Simple Vulkan
  readback. The refreshed evidence reports
  `simpleos_engine2d_source_evidence_usable_status=pass` and
  `simpleos_engine2d_readback_nonblank_status=pass`.
- Windows host Vulkan probe: partial. `vulkaninfo` passes on
  `Intel(R) UHD Graphics 770`, Windows Kit `dxc.exe` is discovered, while
  `glslangValidator`, `spirv-as`, and RenderDoc remain missing:
  `simpleos_windows_vulkan_host_readiness_status=blocked:sdk-tools-missing`.
- RenderDoc release artifacts: missing. `simpleos_renderdoc_rdc_status=missing`
  and `simpleos_wm_renderdoc_log_compare_reason=missing-qemu-and-host-renderdoc-logs`.
- Rebuild note: the RV64 desktop-service kernel now has current built-live QEMU
  evidence in `build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop-built-live-current.env`.
  This Engine2D checker consumes the rebuilt QEMU screendump and saved direct
  Simple Vulkan readback; the remaining fail-closed gap is RenderDoc/SDK tool
  availability, not the RISC-V C++ cross compile path.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\engine2d-renderdoc-out-of-tree.env
Pop-Location
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\engine2d-renderdoc-windows-current.env -Engine2dEvidencePath build\simpleos_multiconfig_live_evidence\vulkan-engine2d-readback-final.env -ProbeHostVulkan
```

The command exits fail-closed because RenderDoc artifacts and two Vulkan SDK
tools are not complete, but the source bridge, saved direct Simple Vulkan
readback, QEMU readback, Windows Kit `dxc.exe`, and Windows Vulkan host probe
rows now report current repo-root-stable evidence.
