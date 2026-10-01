<!-- codex-design -->
# Simple 2D and web renderer GPU optimization architecture

## Decision

Use one surface-owned `GpuRenderSurface` capsule between DrawIR producers and
Engine2D backends. It owns retained buffers, frame slots, damage generations,
submission tokens, and teardown. Display and evidence are separate operations.

```text
input -> semantic event -> scene delta + damage generation
      -> surface.submit(delta) -> backend submit token -> frame ring
      -> nonblocking poll/retire -> device present

explicit capture -> wait named token -> device readback -> exact checksum
```

## Contracts

- `GpuRenderSurfaceId`: stable surface plus device generation; resize/device
  loss invalidates prior tokens and buffers.
- `GpuFrameSlot`: fixed two-or-three-entry ring containing command, staging,
  damage, submit token, and lifecycle state.
- `GpuSubmissionToken`: backend identity, monotonically increasing submission
  id, fence/timeline value, submitted timestamp, and completion state.
- `GpuPresentReceipt`: device/backend identity, frame/damage generations,
  upload bytes, readback bytes (zero), fallback, and completion provenance.
- `GpuCaptureReceipt`: explicit readback source, byte count, exact checksum,
  and the completed submission token it captures.
- `GpuSurfaceMemoryReceipt`: retained allocation count/bytes by purpose and
  lifecycle cause (`create`, `resize`, `device-loss`, `shutdown`).

## Ownership and lifecycle

The web presenter/session creates one surface per backend/device/extent. Cache
lookup returns the owner, never a bare Engine2D instance. Resize first stops new
submissions, retires completed slots, waits only outstanding named tokens,
releases extent-dependent buffers, increments generation, then allocates once.
Device loss invalidates every token and fails closed. Shutdown drains and frees
all retained state. Process-lifetime caches without explicit teardown are not
admitted.

## CPU/GPU interaction

Steady frames upload only packed changed DrawIR ranges and referenced resource
deltas. No full-scene serialization, full framebuffer upload, pixel fingerprint,
or readback occurs on the display path. Exact A/B and framebuffer comparison
run only through `capture(token)` outside the timed interval. Hot emulated
primitives are compacted into bounded indirect commands or device kernels;
unsupported operations retain explicit fallback receipts.

## Async and event semantics

Enqueue is not completion. Backends create a real fence/timeline-backed token;
poll advances submitted to device-complete without blocking, and retire makes a
slot reusable. With all slots busy, policy may coalesce newer damage but may not
overwrite submitted resources or silently block. Input ordering stays on the
CPU semantic owner; each accepted event increments an event generation and
produces deterministic scene/resource deltas. A completed host queue packet is
never labeled GPU completion.

## Benchmark boundary

C Vulkan and Simple Vulkan execute the same packed scene, extent, warmup/sample
count, present/readback mode, and device. Chrome and Simple web measure the same
warm navigation/event-to-pixels-complete boundary. Correctness performs one
explicit readback after timing. Ratio admission requires both records measured,
matching workload/interval metadata, known GPU identity, and no fallback.

## Failure policy

Missing device identity, fence, teardown receipt, buffer accounting, compatible
comparison metadata, or trusted native binary yields unavailable/fail—not zero
time, synthetic data, or CPU fallback promoted as GPU evidence.
