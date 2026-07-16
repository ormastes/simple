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
- Source bridge audit: blocked. The current evidence remains
  `blocked:desktop-service-not-wired-to-vulkan-engine2d-session`.
- Engine2D readback promotion: blocked. The source evidence is browser-backing
  only with Simple readback not run, so
  `simpleos_engine2d_readback_nonblank_status=blocked:source-evidence-not-usable`.
- RenderDoc release artifacts: missing. `simpleos_renderdoc_rdc_status=missing`
  and `simpleos_wm_renderdoc_log_compare_reason=missing-qemu-and-host-renderdoc-logs`.

## Evidence Command

```powershell
Push-Location $env:TEMP
powershell -NoProfile -ExecutionPolicy Bypass -File C:\Users\ormas\dev\simple\scripts\check\check-simpleos-engine2d-renderdoc-evidence.ps1 -EvidencePath build\simpleos_multiconfig_live_evidence\engine2d-renderdoc-out-of-tree.env
Pop-Location
```

The command exits fail-closed because the source bridge and RenderDoc artifacts
are not complete, but the Windows wrapper now reports the current artifacts from
repo-root-stable paths.
