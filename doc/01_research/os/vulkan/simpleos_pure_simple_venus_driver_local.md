<!-- codex-research -->
# SimpleOS pure-Simple Venus driver: local research

Status: design input only, 2026-08-08.  This document does not claim a live
Vulkan device, a working Venus transport, or CPU fallback rendering.

## Current state and constraints

- `src/os/drivers/virtio/virtio_gpu.spl` owns one control virtqueue and fixed
  command/response DMA buffers.  `virtio_gpu_types.spl` has the 2D commands,
  3D/blob constants, and a 24-byte control header model; its comment currently
  calls the final word padding, although the protocol requires a `ring_idx`.
- `virtio_gpu_capset.spl` already provides bounded index walking as
  `GpuCapset {id:u32, max_version:u32, max_size:u32}` and feature gates.  It
  cannot safely expose a variable capset payload beyond `resp_buf` without a
  bounded response allocation.  It also contains a nominal Venus id constant;
  it must not decide capability from that constant alone.
- `virtio_gpu_init.spl` negotiates VIRGL, RESOURCE_BLOB, and CONTEXT_INIT for a
  modern device.  It does not locate the PCI shared-memory capability, create a
  3D context/blob, map host-visible memory, or issue `SUBMIT_3D`.
- `src/os/compositor/vulkan_compositor_backend.spl` intentionally rejects all
  drawing and has `is_available() == false`.  Its honest behavior and tests
  must remain the failure floor until the session and a readback proof exist.
- `src/lib/nogc_async_mut/gpu/vulkan_icd_virtio.spl` is explicitly a fabricated
  counter/opcode model per the existing protocol-facts document; it is not a
  Venus serializer and is not an implementation base.
- Existing `GpuCompositorBackend` is an old pixel-by-pixel virtio 2D route.
  It must not be reused as Venus transport or readback evidence.

## History / prior design findings

`doc/01_research/os/vulkan/venus_virtio_gpu_protocol_facts.md` records the
important correction: the Venus capset is a version/feature handshake, not a
ring-layout record; the guest creates ring geometry and announces it via the
real generated Venus command.  It also records host-visible shared-memory id
1, the need for `ring_idx` plus `FLAG_INFO_RING_IDX` on ring fences, and an
unverified local QEMU GL module.  `simpleos_vulkan_render_backend_plan.md`
requires DrawIR/GpuRenderPlan lowering only after device-backed, bit-exact
evidence.  This design narrows the first milestone to a transport/session and
one exact readback, not a general Vulkan ICD or compositor replacement.

## Local design risks

1. A single mutable `cmd_buf`/`resp_buf` permits neither simultaneous request
   ownership nor variable capset response ownership.  The new session serializes
   control requests and uses one explicitly bounded `VenusControlBuffer`.
2. `max_size` is host-controlled.  All allocations must reject zero and values
   above `VENUS_MAX_CAPSET_BYTES` before DMA/map operations.
3. Shared memory is a PCI capability, not a RAM pointer inferred from a blob
   result.  Missing, malformed, out-of-range, or overlapping BAR windows are a
   non-recoverable `SharedMemoryUnavailable` result.
4. The generated Venus wire format is source/version coupled.  No guessed
   command enum, field layout, or capset-id test may transition availability.

## Canonical artifact ownership

The later interface freeze in
`doc/04_architecture/simpleos_venus_gpu_stack.md` is canonical and supersedes
any alternate names proposed by this research draft.  The common facade is
`GpuAccelerationProvider`; the transport owner is
`VirtioGpuDiscoveryProvider`/`VirtioGpuDiscoveryReceipt`; and the private
Venus subtree is `src/os/drivers/virtio/_Venus/` with `VenusCapsetTuple`,
`VenusProtocolProbe`, `VenusSession`, `VenusCommandQueue`,
`VenusFenceReceipt`, and `VenusDeviceReadbackReceipt`.  Only immutable receipts
cross to the existing `VulkanCompositorBackend`; it never sees PCI BARs,
capset bytes, or raw command data.
