<!-- codex-design -->
# Engine2D Four-Backend Capture Detail Design

## Frozen API

- `Backend2dEventReceipt`
- `Backend2dCaptureEvidence`
- `Backend2dCaptureComparison`
- `backend_2d_capture_evidence`
- `backend_2d_validate_capture`
- `backend_2d_compare_capture`

## Frozen manual flow

1. launch backend
2. render deterministic scene
3. deliver input events
4. capture framebuffer
5. compare evidence

## Scene

The scene has a non-black background, opaque and alpha-blended rectangles,
clipping, an image blit, vector text, and a visible event-state marker. Logical
coordinates are fixed and scaled once to physical pixels.

## Evidence

Every lane emits backend, target, dimensions, DPI, pixel SHA-256,
non-background bounds, ordered event receipt, capture path, and source
revision. GPU adapters additionally retain device/readback receipts. SIMD
adapters retain feature, hit/chunk counters, and scalar-parity receipts in
their backend-specific evidence.

## Comparison

Metadata and event order are exact. CPU SIMD is the exact semantic oracle.
GPU/vector-font pixels may use the existing named tolerance profile, but
geometry and event mismatches always fail. QEMU x86_64 and ARM64 are compared
both to the host oracle and to each other.
