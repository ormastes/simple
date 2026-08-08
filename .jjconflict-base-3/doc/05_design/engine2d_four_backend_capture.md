<!-- codex-design -->
# Engine2D Four-Backend Capture Detail Design

Related WM/Web material detail design:
`doc/05_design/wm_glass_theme_host_simpleos.md`, with execution lanes in
`doc/03_plan/agent_tasks/wm_glass_theme_host_simpleos.md`. Its CPU pixel oracle
is only a prerequisite for the backend evidence designed here.

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

Every lane emits backend, target, scene ID, dimensions, DPI, pixel SHA-256,
non-background bounds, ordered event receipt with its target-side delivery
source, capture path, source revision, and execution provenance. GPU adapters
retain device/readback identity and reject CPU fallback. SIMD adapters retain
feature identity, hit/chunk counters, and scalar-parity receipts.

The bounded CPU-composited glass-material unit path may be used while building
the future scalar oracle, but is not that oracle: it has no SIMD feature/hit
receipt, platform capture, target-side event receipt, or device identity.
Vulkan and Metal records remain invalid unless their own device-origin
readback rejects CPU/mirror fallback.

The helper's opaque transport color, translucent style request, blur-30 to
blur-4 reduction, `i64` arithmetic, and 67,108,864-pixel memory cap are local
CPU semantics. They neither select Vulkan/Metal nor alter the four-backend
evidence schema.

## Comparison

Metadata and event order are exact. CPU SIMD is the exact semantic oracle.
GPU/vector-font pixels may use the existing named tolerance profile, but
geometry and event mismatches always fail. QEMU x86_64 and ARM64 are compared
both to the host oracle and to each other.
