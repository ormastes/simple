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


---

## Lane disposition 2026-11-13 (p3-misc-b)

SimpleOS release/admission/artifact-blocked item per in-file status; requires the SimpleOS target-artifact pipeline and owner lanes this Windows seed lane cannot run. No change from this lane.
---

## Lane disposition 2026-11-22 (simpleos-loader-gaps) — verification-pending

Status: verification-pending. The "no verifier consumes the token" / "partial
consumer" text is stale at `release/1.0.0`:

- Verifier: `executable_admission_pipeline.spl:333`
  `executable_loader_admit_authenticated_open_binding_v1` re-reads the retained
  handle, re-hashes it, checks the canonical manifest hash, runs
  `executable_loader_signature_verify_trusted_v1`, derives load ranges from
  `elf_authenticated_layout_v1`, and issues the token with entry identity
  (`executable_authority_issue_verified(..., true, entry_point)`).
- Consumer: the token is consumed exactly once through
  `executable_loader_retrieve_once` by scheduler adoption
  (`scheduler_executable_adoption.spl:196`, `scheduler_arm32_executable_adoption_v1.spl:178`,
  `scheduler_x86_32_executable_adoption_v1.spl:140`); commit refuses slots without
  entry identity (`executable_authority_registry.spl:303`), so tokens from the legacy
  caller-boolean `executable_loader_admit_open_binding` (no production callers) cannot
  reach adoption.

Remaining blockers (unchanged, need owners/evidence):
- Page mapping / adoption of an already-mapped lease is unverified: QEMU was down.
- ARM64/RISC-V address-space reclaim is still boot-lifetime (`RollbackUnavailable`).
- Unit evidence is red for reasons outside this lane: `executable_admission_pipeline_spec`
  3/6 (spec constructs `ExecuteOpenBinding._owner_nonce`, a field that no longer exists) and
  `executable_load_consumer_spec` 5/9. Diff vs `58c57b730c9` is mixed forward fixes plus
  `os.kernel.arch` -> `os.kernel.hal` drift, not a clean rewind; not restored here.
