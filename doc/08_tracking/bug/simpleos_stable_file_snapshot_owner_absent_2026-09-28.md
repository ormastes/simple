# SimpleOS stable file snapshot owner is absent

**Status:** open. **Scope:** signed catalog boot ingestion, authenticated argv
file bindings, and SimpleOS release evidence provenance. **Inspected:**
`origin/main` at `e4243e67153` on 2026-09-28.

`src/os/kernel/loader/signed_catalog_snapshot_reader_v1.spl` imports
`StableFileSnapshotLeaseV1` and `StableFileSnapshotSealV1` from
`std.fs_driver.mount_table`. It calls `open_stable_snapshot`,
`begin_stable_snapshot_promotion_hash_v1`, `read_stable_snapshot`,
`finish_stable_snapshot_v1`, and `close_stable_snapshot`. The argv binding
owner calls the same API. None of these types or methods is defined in
`src/lib/nogc_async_mut/fs_driver/mount_table.spl`. The argv owner explicitly
calls its open/seal records temporary local views.

This is on the path for signed catalog media boot and for the Simple/Clang
guest toolchain's source, object, and generated executable bindings. Source
presence in those callers does not prove a runnable cold-boot or release
producer while the imported owner contract is absent.

## Required owner contract

- Open one canonical read-only file through the canonical VFS owner and retain
  its handle, mount/namespace/file generation, size, and bounded lease identity.
  Do not require execute permission for source and catalog data.
- Admit a single promotion hash stream. Read exact sequential bytes from the
  retained handle with bounded chunks, reject short reads or changed identity,
  and validate EOF. `finish` must compare the caller digest to owner-tracked
  bytes and recheck live identity; a caller-provided digest alone is not proof.
- Keep the seal usable for the argv owner's second `finish` after guest
  execution, then close exactly once. Catalog readers retain immutable seals
  after close; close must reject lease reuse without retroactively invalidating
  those seals. Stale, cancelled, failed, and partially cleaned leases must not
  become promotable or leak open handles.
- Account for `MountTable` value copies and writes through other table aliases
  or providers. A mount-wide generation stored only in one copied table value
  cannot authenticate mutations made through another copy. Pin a unique live
  VFS owner and use a file identity/generation or equivalent retained handle
  evidence before publishing a seal.
- Migrate the argv owner's temporary `_StableSnapshotOpenView` (`lease: any`)
  and its local `StableFileSnapshotSealV1` to the canonical MountTable records.
  Adding canonical types without changing these callers leaves two unrelated
  record identities and does not complete the source closure.

## Acceptance evidence

Compile the actual catalog and argv caller closures with a source-matched
pure-Simple runtime. Exercise live read/hash/seal/second-finish/close, then
negative cases for forged digest, changed bytes or size, wrong lease/table,
lease reuse after close, hash-order violation, short read, generation change during
execution, cancellation, and cleanup failure. Retain a cold-boot guest run
whose toolchain and reboot/read receipts are bound to the sealed bytes before
claiming `UP-AC-006` or `REQ-018..019` satisfied.
