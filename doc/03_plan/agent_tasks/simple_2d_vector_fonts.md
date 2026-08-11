# Simple 2D Vector Fonts Agent Tasks

| Lane | Status |
|---|---|
| Source/history sidecar | Complete |
| Tests/docs sidecar | Complete |
| Domain sidecar | Complete |
| Architecture sidecar | Complete |
| SSpec/manual sidecar | Complete |
| Performance sidecar | Complete |
| Implementation + merge owner (`/root`) | Active |
| Generated-manual owner (`/root`) | Pending |
| Final normal/highest-capability reviewer (`/root`) | Pending |

Shared interfaces, manual step names, helper names, and fail-fast placeholder rule live in `.spipe/simple-2d-vector-fonts/state.md`. Preserve unrelated dirty SIMD/Metal/compiler work, especially the current `CpuBackend.create_simd` Engine2D edit.

## Current snapshot (2026-08-01)

- Non-bootstrap smoke checks run in this lane:
  - `bin/simple run test/02_integration/rendering/sfnt_glyf_bungee_native_probe.spl`
  - `bin/simple run test/02_integration/rendering/font_renderer_bungee_native_probe.spl`
- Both probes currently report `pass`.
- Checks run:
  - `bin/simple check examples/06_io/ui/graphics_2d_showcase.spl`
  - `bin/simple check src/compiler/50.mir/_MirLowering/module_lowering.spl`
  - both passed.
- Pending work remains for this lane:
  - produce and review the generated manual for vector-font rendering evidence,
  - complete Vulkan/Metal host/WM sequence and QEMU acceptance lanes as ordered in `macos_vulkan_metal_host_qemu_rendering_completion.md`.
