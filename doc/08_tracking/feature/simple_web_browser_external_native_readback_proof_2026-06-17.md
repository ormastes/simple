# Simple Web Browser External Native Readback Proof

**Status:** blocked

## Request

Complete the environment-bound native rendering proof for the Simple Web browser
production hardening lane on hosts that this Linux checkout cannot emulate:
macOS Metal, AMD ROCm/HIP, Windows DirectX, and real browser WebGPU
`device_readback`.

## Rationale

Local Linux evidence covers the browser hardening implementation, renderer
parity, Vulkan/CUDA/OpenCL rows, and explicit host-unavailable states. Release
completion still requires accepted native device-readback evidence for the
remaining platforms, captured with
`doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`.

Local Baseline from 2026-06-17 before external handoff:

- authenticated `/api/state` and `/api/widgets` `200 OK` JSON responses with
  no-store/no-cache/nosniff headers
- normal/shared-WM `/wm.js` and `/retained_renderer.js` script responses with
  no-store/no-cache/nosniff headers
- shown `/wm/native_window` HTML response headers
- hidden unknown-route JSON `404 not_found` fallback headers
- 6-scenario live endpoint pass in
  `test/03_system/gui/simple_web_browser_production_hardening_spec.spl`

## Acceptance

- Metal manifest uses
  `doc/09_report/simple_web_browser_external_host_evidence_manifest_template.md`,
  is accepted by runbook criteria, and has
  `metal_generated_2d_readback_status=pass` plus
  `metal_engine2d_framebuffer_readback_status=pass`.
- ROCm/HIP manifest uses the manifest template, is accepted by runbook
  criteria, and has `rocm_generated_2d_readback_status=pass`.
- DirectX manifest uses the manifest template, is accepted by runbook criteria,
  and has `directx_native_readback_status=pass` with `device_readback` source,
  positive handle, and matching checksums.
- WebGPU manifest uses the manifest template, is accepted by runbook criteria,
  and has `webgpu_real_readback_status=pass`,
  `webgpu_real_readback_source=device_readback`, positive backend handle, and
  matching checksums.
- Parent feature `SIMPLE_WEB_BROWSER_PRODUCTION_HARDENING_2026_06_16` is not
  marked `done` until these manifests are accepted or requirements are
  explicitly re-scoped.
