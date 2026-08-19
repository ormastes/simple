# Metal engine2d backend has no Linux emulation lane — blocked on non-macOS hosts

- **Date:** 2026-08-19
- **Status:** BLOCKED (environment), honest gate — not a code defect
- **Area:** rendering / engine2d backend matrix

## Evidence

Real browser launch on this Linux host (backend-resolve log):

```
[backend-resolve] metal rejected: unavailable: Metal requires macOS
```

Source of the gate:
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:286-291` — `probe_metal()`
  returns `BackendProbeResult.unavailable("metal", "Metal requires macOS")`
  whenever `is_macos()` is false, before any session init is attempted.
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:393-399` —
  `MetalBackend.init()` hard-fails off macOS with
  `last_error = "Metal requires macOS"`.
- `src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl:154` — the nogc session
  layer carries the same gate.

## Why no emulation lane exists

Unlike DirectX (which has an honest Linux compatibility path,
`directx-software-emulation`, backed by a DXVK/vk-ICD probe plus CPU raster,
plus a separate `directx-on-vulkan` lane), there is no MoltenVK-reverse-style
shim (Metal-on-Vulkan) or software-Metal RenderBackend anywhere in
`src/lib/gc_async_mut/gpu/engine2d/`. `src/lib/gc_async_mut/processing/metal_emulator.spl`
exists but is a compute-pipeline emulator for the processing layer, not a
`RenderBackend` — it cannot serve the engine2d render lane.

## Verdict

The metal backend config cannot be exercised on this host. The rejection is
honest and correct; do not fake a lane. Coverage on Linux is limited to the
availability contract, pinned by
`test/02_integration/rendering/backend_emulation_spec.spl`
("metal availability" context: on non-macOS the probe must report exactly
"Metal requires macOS").

## Unblock options (if ever wanted)

1. Run the existing lane on a real macOS host
   (`test/02_integration/rendering/macos_metal_2d_live_harness.spl`).
2. Implement a disclosed `metal-software-emulation` RenderBackend mirroring the
   DirectX pattern (honest renamed lane, CPU raster, probe-gated).
