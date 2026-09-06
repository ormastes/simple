<!-- codex-design -->
# Engine2D Four-Backend Capture Architecture

## Boundary

`DrawIrComposition` remains the common semantic input. Hosted GPU, hosted CPU,
and SimpleOS framebuffer owners lower it independently. The comparison layer
observes immutable evidence and never becomes a renderer.

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
