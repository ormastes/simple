<!-- codex-architecture -->
# SimpleOS Venus GPU stack architecture

Status: accepted interface freeze for the discovery slice, 2026-08-08. It does
not claim Vulkan execution.

## Decision

Use one vertical virtual capsule with public-to-next-layer contracts only:

```text
GpuAccelerationProvider (common public capability)
  -> VirtioGpuDiscoveryProvider (transport/device-config owner)
    -> VenusProtocolSession (Venus sibling-private owner)
      -> VenusCommandQueue/Fence/DeviceReadback (session-private)
        -> VulkanCompositorBackend (existing adapter)
          -> DrawIrComposition / Engine2D (existing execution owner)
```

Sibling layers do not import each other's private structs. The compositor sees
only provider capability and execution receipts; it never parses PCI, capsets,
Venus bytes, queue descriptors, or fence memory.

## Frozen interfaces and files

| Layer | Stable interface | Intended owner file |
|---|---|---|
| Common | `GpuAccelerationProvider`, `GpuProviderCapabilityReceipt`, `GpuExecutionReceipt` | `src/lib/common/gpu/acceleration_provider.spl` |
| Transport | `VirtioGpuPciCapability`, `VirtioGpuDeviceConfig`, `VirtioGpuSharedMemoryRegion`, `VirtioGpuDiscoveryReceipt`, `VirtioGpuDiscoveryProvider` | `src/os/drivers/virtio/virtio_gpu_discovery.spl` |
| Venus | `VenusCapsetTuple`, `VenusProtocolProbe`, `VenusSession` | `src/os/drivers/virtio/_Venus/protocol.spl` |
| Queue | `VenusCommandQueue`, `VenusFenceReceipt`, `VenusDeviceReadbackReceipt` | `src/os/drivers/virtio/_Venus/queue.spl`, `fence.spl`, `readback.spl` |
| Adapter | existing `VulkanCompositorBackend` | `src/os/compositor/vulkan_compositor_backend.spl` |

The first implementation slice may add only transport discovery types and
tests. Later files must not be created as successful stubs; an unresolved
layer remains absent or explicitly rejecting.

## Ownership and lifetime

`VirtioGpuDriver` owns PCI capability mappings, config generation, controlq,
DMA buffers, and the discovery receipt for exactly its device lifetime. A
future `VenusSession` borrows the validated transport facts and owns contexts,
blob resources, rings, queues, and fences. A device reset invalidates every
downstream receipt and session. `GpuExecutionReceipt` is immutable frame
evidence and owns no transient atlas, mapping, or queue memory.

## Admission states

1. `unavailable`: required PCI/device configuration is absent or malformed.
2. `transport-ready`: DEVICE_CFG and bounded capability facts are valid.
3. `venus-discovered`: a complete candidate tuple and host-visible region are
   present; still Ready, never Pass.
4. `device-executed`: reserved for real submit plus known fence completion.
5. `readback-proven`: reserved for same-frame device-origin bytes and checksum.

Only state 5 can make the existing compositor's Vulkan row available. Any CPU
render, scanout screenshot, QEMU option, synthetic handle, or partial receipt
keeps the Vulkan adapter unavailable.

## Fail-closed rules

- Bound PCI visits to 48 and capsets to 64; reject loops and duplicates.
- Reject capability lengths below 16 bytes (base) or 24 bytes (64-bit shared
  memory), BAR indexes above 5, zero lengths, address overflow, and regions not
  proven inside their BAR.
- Read `num_capsets` only from DEVICE_CFG offset 12, with stable config
  generation; never from common config.
- Reject capset payload sizes above 4072 bytes for the current response buffer.
- Retain partial tuples for diagnostics but mark the receipt partial and
  promotion-ineligible.
- Never infer a Venus Pass from capset ID, render-node existence, or feature
  bits. Exact protocol classification remains a Venus-layer responsibility.

## Architecture variants

PCI capability parsing is shared by x86_64 and PCI-backed ARM/RISC-V. MMIO
adapters provide equivalent typed device-config facts through the same
transport interface. They cannot expose architecture-specific provider,
Venus, queue, or compositor types. Physical boards without virtio-gpu require
a separate native GPU provider under the same common capability contract.

## Differential-conformance capsule (2026-08-08 addendum)

The shared surface is semantic trace data, never a renderer or GPU API:

```text
common immutable NormalizedTrace / TraceEvent schema
  -> GPU trace projection ---------> TraceComparator <--------- Mesa/Vulkan ReferenceOracleAdapter (test only)
  -> Web trace projection ---------> TraceComparator <--------- Chrome ReferenceOracleAdapter (test only)
```

`TraceEvent` fields are frozen as `schema_version`, `run_id`, monotonically
increasing `sequence`, normalized/relative `monotonic_ns`, `layer_id`,
`operation`, normalized `object_id` and `parent_id`, `result_class`,
`error_class`, stable scalar fields/payload digest, and
`environment_profile_id`. Layer IDs are `virtio_transport`, `venus_protocol`,
`vulkan_api`, `draw_ir`, `web_layout`, and `web_paint`. Raw addresses, native
handles, host timestamps, allocator details, and incidental call order never
cross the projection boundary.

The generic schema and injected sink are the only common nodes production
instrumentation may import; the sink is a no-op outside conformance builds.
`TraceComparator`, `GpuEnvironmentProfile`, handle maps, and
`ReferenceOracleAdapter` live in test support. GPU and Web adapters import the
generic comparator separately and cannot import each other. Oracle output can
fail a test but cannot produce `GpuProviderCapabilityReceipt`,
`GpuExecutionReceipt`, compositor availability, or CPU fallback.

The SFFI boundary is a compiled-host test leaf. Dynamic Mesa/Vulkan discovery,
opaque handles, calls, and release functions have exactly one extern owner in
the canonical no-GC synchronous backend. The safe test adapter owns each
instance/device/queue/resource handle, closes in reverse order, rejects use or
double close after release, converts every foreign result into a typed error,
and records normalized IDs before comparison. Compatibility families re-export
that owner; no test file declares duplicate externs.

### GPU expectation profiles

`GpuEnvironmentProfile` references, rather than duplicates, the canonical IDs
`simpleos-qemu-x86_64-vulkan-virtio`,
`simpleos-qemu-aarch64-vulkan-virtio`, and
`simpleos-qemu-riscv64-vulkan-virtio`. Each adds expected transport, required
VirtIO feature conjunction, Venus protocol/version range, Vulkan API/device
identity predicates, oracle library/driver identity, device-origin-readback
requirement, and `fallback_used=false`. A mismatched or unavailable environment
is Blocked/Fail according to the canonical profile; it is never silently
reclassified or compared against a different oracle.

### VUDA decision

VUDA is not in the repository and its CUDA-compatible C++ Vulkan ownership
does not align with any frozen layer. It is deprecated as a production or
migration candidate and must not be vendored. If an external VUDA compute
fixture is retained, it stays outside the provider/transport/Venus capsule and
is labelled `external_compute_reference`; it cannot serve as render evidence.
