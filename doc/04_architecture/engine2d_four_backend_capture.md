<!-- codex-design -->
# Engine2D Four-Backend Capture Architecture

Related semantic/material architecture:
`doc/04_architecture/wm_glass_theme_host_simpleos.md`, implemented according to
`doc/03_plan/agent_tasks/wm_glass_theme_host_simpleos.md`. This document begins
at the backend capture boundary and does not redefine Web/WM material policy.

## Boundary

`DrawIrComposition` remains the common semantic input. Hosted GPU, hosted CPU,
and SimpleOS framebuffer owners lower it independently. The comparison layer
observes immutable evidence and never becomes a renderer.

The CPU-composited glass material helper is an Engine2D implementation detail
below this boundary: it consumes existing styled-rectangle keys and produces
ordinary CPU pixels before a capture adapter observes them. It creates no
`Backend2dCaptureEvidence`, does not select a backend, and cannot establish
CPU-SIMD, Vulkan, Metal, host, or QEMU execution.

Its native-safe transport color remains opaque fallback while translucent
material stays in style metadata; requested blur 30 is reduced to bounded blur
4 and the helper caps output/working storage at 67,108,864 pixels. These are
implementation witnesses only, not capture evidence.

## Layers

1. **Scene producer:** deterministic scene and event sequence.
2. **Backend adapter:** Metal, Vulkan, CPU SIMD, or SimpleOS SIMD.
3. **Platform capture:** synchronized GPU readback, CPU framebuffer copy, or
   QMP `screendump`.
4. **Evidence adapter:** converts platform receipts to
   `Backend2dCaptureEvidence`.
5. **Comparison:** exact metadata/events plus pixel comparison using the
   existing `wm_compare` tolerance profiles.

## Ownership

- Backend-specific resource state stays in its backend/session owner.
- Host selection stays in `engine.spl`.
- SimpleOS uses the narrow freestanding compositor core.
- `src/app/wm_compare/backend_2d_capture_evidence.spl` owns only normalized
  evidence validation and aggregate acceptance.

## Failure model

Validation returns a stable rejection reason for bad backend names, dimensions,
DPI, hashes, bounds, event order/count/backend, capture path, or revision.
Comparison does not run on rejected evidence. Unsupported events or unavailable
native SIMD remain explicit failures.
