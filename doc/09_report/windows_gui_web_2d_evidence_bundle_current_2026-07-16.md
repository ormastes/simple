# Windows GUI Web/2D Evidence Bundle - 2026-07-16

Current Windows PowerShell run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-windows-gui-web-2d-evidence-bundle.ps1
powershell -NoProfile -ExecutionPolicy Bypass -File scripts\check\check-windows-gui-web-2d-evidence-bundle.ps1 -RequireFullCompletion
```

Default result:

- `windows_gui_web_2d_evidence_bundle_status=pass`
- `windows_gui_web_2d_evidence_bundle_reason=pass`
- `windows_gui_web_2d_evidence_bundle_directx_strict_status=pass`
- `windows_gui_web_2d_evidence_bundle_vulkan_partial_status=pass`
- `windows_gui_web_2d_evidence_bundle_vulkan_full_gate_status=blocked`
- `windows_gui_web_2d_evidence_bundle_d3d12_current_status=pass`
- `windows_gui_web_2d_evidence_bundle_d3d12_full_gate_status=blocked`

Full-completion result:

- `windows_gui_web_2d_evidence_bundle_status=fail`
- `windows_gui_web_2d_evidence_bundle_reason=vulkan-full,d3d12-full`
- `windows_gui_web_2d_evidence_bundle_vulkan_full_reason=sdk-tools,renderdoc-tools,host-readiness,browser-run,browser-events,browser-backing,renderdoc-capture`
- `windows_gui_web_2d_evidence_bundle_d3d12_full_reason=compare-status,native-d3d12-readback,browser-d3d12-backing,pairwise-argb-diff,argb-source-evidence,pix-gpu-debugger-gate,pix-or-gpu-debugger-status,pix-or-gpu-debugger-artifact`

The default bundle checker validates the current saved evidence set without
rerunning live capture: strict DirectX D3D11 browser/event/GPU-capture proof,
partial Vulkan host proof, and fail-closed D3D12 render-log proof with strict
upstream DirectX diagnostics. `-RequireFullCompletion` is the release-style
strict mode and remains blocked until Vulkan SDK/RenderDoc browser capture and
D3D12/PIX evidence are available.

Primary artifacts:

- `scripts/check/check-windows-gui-web-2d-evidence-bundle.ps1`
- `build/gui-web-2d-directx-env-windows-event-strict-gpucap/evidence.env`
- `build/gui-web-2d-vulkan-env-windows-current-check/evidence.env`
- `build/windows-d3d12-render-log-env-strict-current/evidence.env`
