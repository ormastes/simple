# Engine2D Four-Backend Capture

This scenario verifies that Metal, Vulkan, host CPU SIMD, and SimpleOS QEMU
SIMD captures use one honest evidence contract. SimpleOS runs on both x86_64
and ARM64.

## Primary flow

### 1. launch backend

Launch the requested backend from the integrated source revision. Record the
target and actual backend/device or SIMD execution receipt.

### 2. render deterministic scene

Render the frozen scene at the requested dimensions. GPU work must be complete
before readback; SIMD hit/chunk counters must be greater than zero.

### 3. deliver input events

Inject and receive, in order:

`focus,pointer_move,pointer_down,pointer_up,key_down,key_up`

Injection without a target-side delivery receipt fails.

### 4. capture framebuffer

Write a durable PPM or PNG and record dimensions, DPI, SHA-256,
non-background bounds, capture path, and source revision.

### 5. compare evidence

Validate every record, compare exact dimensions and event order, then report
exact or tolerated pixel differences. Any absent or invalid backend makes the
aggregate result fail.

## Negative cases

- Missing or malformed SHA-256 is rejected.
- QMP-only or wrapper-only event success is rejected.
- Dimension mismatch is rejected before pixel tolerance.
- CPU mirrors labeled as GPU captures are rejected by the backend adapter.
- Scalar fallback labeled as SIMD is rejected by execution-counter checks.
