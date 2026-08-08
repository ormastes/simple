<!-- codex-design -->
# Supplemental detail design: Venus protocol/session

Status: protocol supplement.  Exact types/files are frozen by
`doc/05_design/simpleos_venus_gpu_stack.md` and
`doc/04_architecture/simpleos_venus_gpu_stack.md`; this document adds no
competing API.

## State and ownership refinements

`VirtioGpuDriver` uniquely owns PCI/config/controlq/DMA for its device life.
`VirtioGpuDiscoveryReceipt` is cached immutable evidence and is invalidated on
reset.  A `VenusSession`, created only from a complete receipt, owns context,
blob mapping, guest-authored ring, bounded `VenusCommandQueue`, and monotonic
fence ids.  It cannot publish a `GpuExecutionReceipt` until the corresponding
`VenusFenceReceipt` completes and `VenusDeviceReadbackReceipt` provides
same-frame, device-origin bytes.

The existing single control DMA pair remains serialized: command payload and
used response length are bounded before writes/decodes.  No parallel producer
or retry may overwrite an unknown submitted command.  Queue capacity is three;
full, timeout, response mismatch, or device loss returns an unavailable/error
receipt and invalidates the session.

## Test ownership refinement

Protocol fixtures must be generated/pinned from the exact upstream Venus
revision; a manual opcode or layout cannot pass.  Unit tests own capset/payload
limits, BAR containment, stable generation retries, queue full/wrap refusal,
and fence-ring mismatch.  QEMU system evidence owns live tuple transcript,
submit/fence/device-readback/correlated checksum.  Compositor tests prove the
existing backend stays rejecting until that full receipt exists.  Shared helper
names and fail-fast placeholders remain those in the canonical agent plan.
