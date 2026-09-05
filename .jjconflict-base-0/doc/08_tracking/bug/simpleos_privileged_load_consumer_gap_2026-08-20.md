# SimpleOS privileged executable load consumer gap

Status: partially implemented, release-blocking for execution

The loader now owns a bounded four-slot map/release capsule. Its pure planning
model rejects unsupported targets, ABI mismatch, W+X segments, ELF page
congruence failures, arithmetic overflow, user-range escape, segment page
aliases, invalid entry points, and segment/total page-budget excess. The
privileged adapter consumes an opaque loader authority once, reads at most 64
MiB from the retained handle in bounded chunks, verifies the exact SHA-256,
re-admits ELF structure, rebuilds and matches the process image, checks stack
overlap/page budget, and maps through `_map_user_process_image`.

Only a native x86_64 build loading an x86_64 plan reaches allocation. Mapping
failure rolls back by destroying the whole address space; successful mapping remains in a private generational slot
until release. Close failure clears the mapped resource but keeps the authority
in `CloseRetryable` for retry. A mutation committed before an unlock error is
never treated as absent: reservation is quarantined, mapped ownership transfer
is retained, and lease transitions cannot double-destroy or reuse a resource.

The narrow cross-layer visibility seam exports compile-time architecture
identity, the opaque `AddressSpace` and read-only process-image
records/accessors, address-space create/destroy, and the scheduler-owned
mapping function. Process-image construction stays
package-private to the loader. No task constructor, mutable scheduler state, or
mapping internals are exported.

## Remaining blockers

- Public admission returns `CryptographicVerifierUnavailable`, so production
  callers cannot mint a live authority token.
- Every receipt sets `execution_authorized=false`; the scheduler has no owner
  method that accepts and atomically adopts an already-mapped address-space
  lease without remapping.
- ARM64 and RISC-V address-space destruction is boot-lifetime/no-reclaim, so
  those architectures fail before allocation with `RollbackUnavailable`.
- The focused spec exercises the pure validation and rollback/close-retry
  lifecycle, but runtime/bootstrap execution was explicitly disallowed. Binary
  `pread` transport, raw-mutex failure semantics, concurrent replay, actual map
  rollback, and close retry still require self-hosted target evidence.

No execution-readiness claim follows from this slice.
