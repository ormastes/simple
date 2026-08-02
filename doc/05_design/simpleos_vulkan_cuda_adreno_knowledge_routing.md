# Detail Design: SimpleOS GPU Ports and Knowledge Selection

## GPU records

`ProcessingDeviceRequest` carries ProcessingIR, selected backend, generation,
and correlation IDs. `ProcessingDeviceResult` carries status, backend,
evidence class, provenance, readback metadata, and diagnostic reason.

`VulkanDevicePort` admits only Vulkan render/present receipts.
`CudaHostOffloadAdapter` translates a validated processing request into the
existing ivshmem request and validates the returned CUDA receipt.
`AdrenoTurnipAdapter` supports capability/readiness classification before
native submission is available; unsupported stages fail explicitly.

## Virtio-gpu Venus protocol admission

The staged Venus protocol module is a private SimpleOS driver component, not a
new public GPU port. It consumes an immutable negotiated-capability snapshot and
produces either a validated command plan or a typed rejection. Its records
cover:

- required virtio-gpu feature presence and protocol generation;
- Venus capset ID, version, and bounded advertised/returned size;
- nonzero context, resource, submission, and fence identifiers;
- resource-blob memory class, size, and mapping prerequisites; and
- legal prerequisite order for capset discovery, context creation, resource
  creation/attachment, command submission, fence completion, and readback.

The module now encodes exact packed little-endian request bytes for capset-info,
capset, context-create, zero-entry HOST3D blob-create, fenced submit-3D, and
fenced map-blob commands. Context names are zero-filled to the protocol width;
bounded payload and identifier checks fail before bytes are emitted. Typed
response validation checks the 24-byte header, response class/type, supported
flags, and exact submitted-fence correlation. Unfenced requests require both
the response flag and fence ID to remain zero.

The admission result and wire codec contain no fabricated queue index, device
address, Vulkan handle, fence completion, or readback checksum. Valid bytes and
an accepted synthetic response remain `unsupported` as execution evidence
until the transport owner submits real virtqueue descriptors and validates the
device-owned response.

Protocol records are invalidated on virtio device reset, feature renegotiation,
capset change, or protocol-generation change. Submission identifiers are not
reused across an invalidation boundary.

## Bounded controlq seam

`virtio_gpu_venus_controlq` is the implemented bounded leaf. It accepts already
encoded request bytes plus expected response type/fence, delegates synchronous
descriptor submission to the current virtio-gpu controlq owner, and passes the
returned response header to `venus_validate_response`. Its current transport
failure is intentionally collapsed to `controlq-timeout-or-sync`; distinct
queue-full, timeout, reset generation, used length, and ownership results remain
required before native promotion. It does not duplicate the wire codec, Vulkan
ICD, blob mapping policy, or evidence promotion policy.

## Environment discovery

`virtio_gpu_venus_environment` normalizes five independent inputs only after
validation: host feature mask, negotiated feature mask, device-reported capset
count and rows, PCI shared-memory rows, and capset-query-fix behavior. Required
bits are VIRGL, RESOURCE_BLOB, and CONTEXT_INIT. Negotiated bits must be a
subset of offered bits; capset cardinality must match the enumerated rows; and
exactly one valid Venus capset and one nonzero `HOST_VISIBLE` region must exist.
The resulting record may open the bounded controlq gate but is not a BAR grant,
Vulkan ICD, or native execution receipt.

## Validation order

1. validate IR and bounded dimensions;
2. validate backend capability and generation;
3. submit without changing semantic backend identity;
4. wait for correlated completion/fence;
5. require device-origin readback;
6. compare byte length, checksum, and every canonical fixture value;
7. publish typed evidence only after all checks pass.

## Knowledge records

The registry contains version, feature groups, feature experts, layer bases,
layer experts, path prefixes, and architecture profile. Selection output
contains matched paths, ordered stable IDs, content hashes, and rejection
reason. Longest-prefix ties are ambiguity errors.

## Error handling

All invalid, stale, unsupported, or incomplete paths return a typed rejected or
blocked result. No adapter manufactures positive handles, changes evidence
class, or falls back while preserving device provenance.

## Test seams

- Pure selectors and validators receive table-driven unit tests.
- Adapter integration tests use an in-memory ivshmem fixture and explicit stale,
  mismatch, timeout, CPU-source, and zero-provenance cases.
- System tests retain the visible steps `Probe the GPU environment`, `Lower
  shared processing IR`, `Submit through the selected Vulkan device`, and
  `Verify device-origin readback`.
- Environment tests retain native QEMU/UNO Q blockers and exact resume commands.
- Device-free Venus admission tests cover missing feature bits,
  wrong/unsupported capsets, zero identifiers, empty submission, and valid
  planning. Eight byte-level scenarios additionally prove exact little-endian
  layouts, fixed-width zero fill, HOST3D profile bounds, submit-size bounds,
  typed response rejection, and exact fenced/unfenced correlation. These tests
  establish protocol and codec coverage only; the current 8/8 result is
  provisional because it used the bootstrap-seed runner.
- Six environment-discovery scenarios cover offered/negotiated feature
  provenance, capset cardinality, exact Venus selection, host-visible SHM, and
  capset-query-fix admission; they are also provisional device-free evidence.
- A later QEMU environment test must independently prove negotiated features,
  Venus capset/ICD identity, shared-memory mapping, real virtqueue submission,
  correlated fence completion, and device-origin readback. It is the only test
  allowed to promote the Venus row to `guest-native`.
