<!-- codex-design -->
# Browser renderer GPU surface owner — selected detail design

**Status:** selected O1 + B/N2; implementation pending runtime/provider admission

## Boundary

`host_compositor_core` owns one device scheduler and a bounded map of child
surfaces. A child surface owns its backing epoch, retained DrawIR/resource
revision, damage accumulator, and frame receipts. Browser/session code owns DOM
and producer revisions and sends frozen snapshots; it never owns Vulkan handles.
The runtime B/N2 session owns command buffers, descriptor/buffer references,
fences/timeline objects, slot capacity, and exact retirement.

The surface API is `gpu_surface_open`, `gpu_surface_offer`,
`gpu_surface_poll`, `gpu_surface_capture`, `gpu_surface_resize`, and
`gpu_surface_close`. Offers return queue acceptance only. Poll returns distinct
compute-complete and presenter-release receipts. The existing synchronous
boolean compositor path uses an adapter until the pending path is migrated.

## State and data flow

Each frame carries device generation, surface backing epoch, producer revision,
resource revision, monotonic frame sequence, and an opaque runtime slot receipt.
The accepted, submitted, completed, and presented cursors are separate. The
surface publishes only the contiguous sequence prefix after exact presenter
release. A frame slot is reusable only after compute completion, presenter
release, and resource release are all proven.

For local damage, each in-flight image has its own predecessor content
revision. If that revision is unavailable, the owner performs an ordered GPU
reseed or full redraw; it never replays damage against unknown contents.

## Pressure, cancellation, and loss

The B/N2 session is constructed with capacity 3–16. When full, the owner polls
the oldest slot once and may perform one configured bounded wait. It then
returns `would-block` without spinning, sleeping, growing, or calling
`wait_idle`. Cancellation closes admission but does not claim GPU preemption;
accepted work drains. Unknown completion/device loss fail-stops the session and
retains all owners until recovery or teardown evidence resolves them.

Resize closes only the affected surface, coalesces the newest extent, and
rebinds after its leases retire. Device loss closes all surfaces on the device,
revokes publication generations, and uses the recovery owner. Close, loss,
retirement, and cancellation are idempotent.

## Capture and compatibility

Display never performs readback. Capture is an explicit operation with its own
receipt and timing counter, and cannot acknowledge display dirty state. Pixel
APIs remain unchanged and may use a scoped compatibility owner; their output is
not display-admission or GPU-performance evidence.

## Observability and acceptance

Record monotonic host p50/p95 offer, poll, bounded wait, compute retirement,
presenter release, and publication latency; report optional Vulkan timestamps
only when available. Count accepted/rejected submissions, backpressure,
in-flight slots, retained/released bytes, CPU waits, unknown completion,
cancellation, and recovery idles. The linked system plans are authoritative;
device-free fixtures cannot admit hardware or performance claims.
