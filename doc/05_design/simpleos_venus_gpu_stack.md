<!-- codex-design -->
# SimpleOS Venus GPU stack detail design

## Discovery data

`VirtioGpuPciCapability` records cfg type, BAR, capability ID, 64-bit offset,
64-bit length, and source capability offset. `VirtioGpuDeviceConfig` records
events, scanouts, raw/admitted capset counts, and config generation.
`VirtioGpuSharedMemoryRegion` records shmid, BAR, physical base, byte length,
and whether containment was proven. `VirtioGpuDiscoveryReceipt` records status,
reason, feature mask, all bounded capset tuples, the optional host-visible
region, architecture/transport, and fixed false execution/readback fields.

## Algorithm

1. Walk the PCI vendor-capability chain with a 48-entry visited-offset table.
2. Decode only supported capability types. Validate minimum size, BAR, 64-bit
   arithmetic, and BAR containment before publishing a mapping.
3. Retain the first supported DEVICE_CFG. Retain shared-memory capabilities by
   ID and reject duplicate IDs; choose host-visible ID 1 without relying on
   order.
4. Read common config generation, then DEVICE_CFG fields, then generation
   again. Retry at most three times if generation changed.
5. Reject `num_capsets > 64`. Query exactly the admitted count through the
   existing controlq and keep every tuple. Stop with `partial` on any failed
   response.
6. Fetch no capset payload larger than 4072 bytes. A discovered candidate
   tuple remains discovery-only.
7. Cache the immutable receipt in `VirtioGpuDriver`; invalidate it on reset.

## Error model

APIs return `Result<T, text>` for invalid wire/config facts and a typed receipt
for environmental absence/partial discovery. Stable reasons include
`pci-cap-loop`, `pci-cap-limit`, `reserved-bar`, `cap-too-short`,
`address-overflow`, `bar-containment-unproven`, `device-config-missing`,
`config-generation-unstable`, `capset-count-over-limit`,
`host-visible-region-missing`, `capset-query-partial`, and
`capset-payload-over-limit`.

## Test seams

Pure decoders consume byte lists or primitive capability records; fake MMIO is
not required. A scripted capset query seam returns typed responses to cover
complete and partial walks. Integration tests may inject a `DeviceGrant` and
recorded PCI capability image. Live QEMU remains a separate environmental gate.

## Future queue slice

`VenusSession` is created only from a complete discovery receipt. It owns typed
context, host-visible blob mapping, guest-authored ring, bounded command queue,
and fence sequence. Readback must originate after the matching completed fence;
the compositor receives only the immutable `GpuExecutionReceipt`. There is no
CPU fallback inside the Venus provider; Engine2D owns explicit fallback.

## Performance and observability

Discovery occurs once. Log bounded counts, tuple values, retry count, selected
shmid, elapsed microseconds, and final state. Do not log arbitrary payloads in
production; a bounded first-16-byte diagnostic capture is permitted only in a
debug evidence artifact. No discovery work is allowed in per-frame execution.
