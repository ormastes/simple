<!-- codex-design -->
# SimpleOS Venus GPU stack detail design

## Discovery data

`VirtioGpuPciCapability` records cfg type, BAR, capability ID, 64-bit offset,
64-bit length, and source capability offset. `VirtioGpuDeviceConfig` records
the validated mapped DEVICE_CFG address, events, scanouts, raw/admitted capset
counts, and config generation.
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

## Differential trace detail (2026-08-08 addendum)

Each layer projects its native input/result into `TraceEvent` at its public
next-layer seam through an injected test sink. Object IDs are assigned per run
by first semantic creation and then resolved through an explicit map; a
missing/double mapping is a comparator error. Byte payloads are represented by
length plus a stable digest, with selected protocol scalars retained by name.
Error results use stable `result_class`/`error_class`; diagnostic strings are
context only.

`NormalizedTrace` contains one schema version, environment profile ID, run ID,
ordered events, drop count, and completion flag. A trace with drops, duplicate
sequence, unknown layer, profile mismatch, or incomplete completion is
comparison-ineligible. `TraceComparator` selects a layer/operation projection,
maps oracle/object identities, and returns equal, divergent, or ineligible with
the first differing event and bounded preceding context.

The GPU oracle adapter dynamically opens Mesa/Vulkan only in a compiled host
test, resolves an exact symbol manifest, queries driver/device identity, runs
the matched operation, waits its own fence, reads its own result, emits the
same semantic projection, and tears down every owned opaque handle in reverse
order. Missing library/symbol/extension, nonzero foreign result, invalid
ownership, timeout, and readback-source ambiguity are typed rejections. No
oracle pointer or Vulkan handle is stored in a trace or production receipt.

The three SimpleOS profiles bind the existing canonical environment IDs. They
add expectations for PCI versus MMIO transport, VIRGL + CAPSET_QUERY +
RESOURCE_BLOB + HOST_VISIBLE + CONTEXT_INIT, Venus protocol range, device and
driver identity patterns, device-origin readback, and no fallback. Tests must
print actual and expected identities and cannot substitute llvmpipe, another
architecture, or a host-only profile without an explicit profile that permits
it.

Frozen ownership after differential-sidecar review:

| Owner | File |
|---|---|
| generic immutable trace schema/injected sink | `src/lib/common/spec/differential_trace.spl` |
| generic comparator/profiles | `src/lib/nogc_sync_mut/test/differential_conformance.spl` (test-only import surface) |
| canonical dynload extern owner | `src/lib/nogc_sync_mut/gpu/reference_oracle_sffi.spl` |
| safe GPU oracle adapter | `src/lib/nogc_sync_mut/test/gpu_reference_oracle.spl` |
| GPU differential specs | `test/03_system/os/qemu/simpleos_venus_differential_spec.spl` |
| Web/Chrome projection consumer | existing `test/05_perf/web_render_chrome/`, importing only generic test support |
