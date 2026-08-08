<!-- codex-architecture -->
# SimpleOS pure-Simple Venus transport capsule (proposed MDSOC architecture)

Status: proposed; no implementation or live-device claim.  This refines, but
does not replace, `simpleos_vulkan_render_backend_plan.md`.

## Decision

Use one `venus` virtual capsule beneath `src/os/drivers/virtio`, with strict
control-transport ownership and a compositing facade.  The capsule is selected
only after physical feature/capset/shm/ring setup succeeds; otherwise it is
absent and `VulkanCompositorBackend` remains rejecting.

## Module tree and visibility

```
src/os/drivers/virtio/
  virtio_gpu.spl                         # existing device/controlq owner
  virtio_gpu_types.spl                   # existing wire primitives; corrected ring_idx
  venus/
    contracts.spl                        # common, immutable next-layer contracts
    capset_selection.spl                 # private enumeration/validation policy
    shared_memory.spl                    # private PCI SHM capability locator/map bounds
    transport/control.spl                # private sole VirtioGpuDriver borrower
    transport/ring.spl                   # private ring producer/fence accounting
    session.spl                          # parent facade/lifetime owner
    provider.spl                         # next-layer public facade only
src/os/compositor/
  vulkan_compositor_backend.spl          # consumes provider facade; no raw transport
```

Tree-private is the default.  `contracts.spl` is the only common node visible
to `session`, `provider`, and compositor.  `transport/*`, PCI maps, raw DMA
addresses, capset bytes, and ring cursors are private to the Venus capsule.
No compositor sibling imports `virtio_gpu_capset` or touches `VirtioGpuDriver`.

| Raw layer | `contracts` common node | public to parent | public to next layer |
|---|---|---|---|
| `capset_selection` | `VenusCapsetSelection`, `VenusInitError` | selection result | none |
| `shared_memory` | `VirtioGpuSharedMemoryRegion`, `VenusInitError` | validated region | none |
| `transport/control` | `VenusControlRequest`, `VenusControlResponse` | synchronous result | none |
| `transport/ring` | `VenusSubmission`, `VenusFenceReceipt` | receipt/result | none |
| `session` | `VenusSessionState`, `VenusReadbackReceipt` | `VenusSession` | provider only |
| `provider` | `VenusRenderProvider` | compositor adapter | compositor only |

## Concrete contracts, ownership, and lifetime

```simple
enum VenusSessionState:
    New
    FeaturesNegotiated
    CapsetSelected
    SharedMemoryMapped
    RingReady
    Failed
    Closed

enum VenusInitError:
    FeatureMissing
    CapsetMissing
    CapsetTooLarge
    CapsetVersionUnsupported
    SharedMemoryUnavailable
    SharedMemoryOutOfBounds
    ProtocolVersionMismatch
    ControlRejected
    FenceTimeout
    DeviceLost
    Closed

struct VenusCapsetSelection:
    id: u32
    version: u32
    bytes: [u8]

struct VirtioGpuSharedMemoryRegion:
    shmid: u8
    bar_index: u8
    phys_base: u64
    byte_len: u64
    mapped_virt: u64

struct VenusRing:
    resource_id: u32
    ring_index: u8
    blob_id: u64
    byte_offset: u64
    byte_len: u64
    write_offset: u64
    completed_offset: u64

struct VenusSubmission:
    sequence: u64
    ring_index: u8
    byte_count: u32
    fence_id: u64

struct VenusFenceReceipt:
    sequence: u64
    fence_id: u64
    ring_index: u8
    completed: bool

struct VenusReadbackReceipt:
    source: text
    fence: VenusFenceReceipt
    width: u32
    height: u32
    pixels: [u32]
    checksum: i64

pub trait VenusRenderProvider:
    fn is_ready() -> bool
    fn unavailable_reason() -> text
    fn submit_draw_ir(payload: [u8]) -> Result<VenusFenceReceipt, VenusInitError>
    fn readback_exact(width: u32, height: u32) -> Result<VenusReadbackReceipt, VenusInitError>
    fn close() -> Result<bool, VenusInitError>

class VenusSession:
    state: VenusSessionState
    selection: VenusCapsetSelection?
    shared_memory: VirtioGpuSharedMemoryRegion?
    ring: VenusRing?
    next_sequence: u64
    next_fence_id: u64
```

`VenusSession` uniquely borrows the initialized `VirtioGpuDriver` for its
whole life.  It owns capset bytes, shared-memory mapping, blob/ring, sequence,
and fence counters.  A provider borrows the session; it cannot outlive it.
`close()` rejects new work, drains/cancels only owned fences, unmaps the blob,
destroys context, then clears the mapping.  No raw pointer escapes a receipt.

## Flow, queue bounds, and errors

1. Negotiate VIRGL + RESOURCE_BLOB + CONTEXT_INIT; enumerate every capset.
2. Read the selected payload into an owned buffer only when `0 < max_size <=
   VENUS_MAX_CAPSET_BYTES` (proposed 64 KiB).  Generated protocol validation
   confirms the matching supported version and blob-id-0 capability.
3. Locate SHM id 1 PCI capability; validate BAR/window arithmetic before map.
4. Create typed context, host3D/mappable blob, map it, then write and submit a
   version-matched generated `vkCreateRingMESA` message.  Ring geometry is
   guest-owned; it is not parsed from capset bytes.
5. `submit_draw_ir` accepts at most `VENUS_MAX_SUBMISSION_BYTES` (1 MiB) and
   at most `VENUS_MAX_IN_FLIGHT` (3) submissions.  It never waits while holding
   a producer slot.  It sets fence + info-ring-index flags and the actual ring
   index.  Full ring/in-flight capacity gives `ControlRejected`, not overwrite.
6. `readback_exact` waits for its receipt using a bounded timeout, copies from
   a device-produced resource only after fence completion, records source,
   fence id, dimensions, pixels, and checksum.  Timeout/device loss closes the
   session and preserves CPU/rejecting fallback; it never manufactures pixels.

No retry loop retransmits a command after an unknown device result.  A control
response type mismatch, malformed length, unrecognized protocol version, or
fence mismatch is fail-closed and observable through `unavailable_reason()`.

## Performance, observability, and non-goals

Bring-up may allocate/map once.  Warm submission target: no allocations,
no full framebuffer readback, at most one control submission and one fence per
frame; target 3 in-flight frames and a 16.7 ms frame budget.  Readback is test
or explicit capture-only, with a 250 ms timeout; it is never a presentation
path.  Counters: setup duration, capset bytes, ring high-water, submissions,
fence waits/timeouts, device losses, readbacks, and CPU-fallback selections.

The capsule deliberately does not implement a complete loader-ABI ICD, Linux
DRM, WSI, host driver, arbitrary Vulkan, or physical-board driver.  QEMU Venus
evidence is labelled `qemu_only` until a separate board-native GPU driver exists.
