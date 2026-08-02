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

The admission result contains no fabricated queue index, device address,
Vulkan handle, fence completion, or readback checksum. An admitted plan remains
`unsupported` as execution evidence until a transport owner encodes it into
real virtqueue descriptors and validates the corresponding device response.

Protocol records are invalidated on virtio device reset, feature renegotiation,
capset change, or protocol-generation change. Submission identifiers are not
reused across an invalidation boundary.

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
- Device-free Venus unit tests cover missing feature bits, wrong/unsupported
  capsets, oversized or truncated payloads, zero/stale identifiers, illegal
  prerequisite order, valid admission, and invalidation. These tests establish
  protocol-structure coverage only.
- A later QEMU environment test must independently prove negotiated features,
  Venus capset/ICD identity, shared-memory mapping, real virtqueue submission,
  correlated fence completion, and device-origin readback. It is the only test
  allowed to promote the Venus row to `guest-native`.
