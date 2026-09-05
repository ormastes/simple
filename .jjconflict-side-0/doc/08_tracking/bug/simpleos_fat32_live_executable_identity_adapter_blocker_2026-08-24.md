# FAT32 live executable identity adapter blocker (2026-08-24)

## Status

Blocked fail-closed. The committed point-in-time identity owner must not be
wired to launch yet.

## Evidence

- `Fat32Filesystem.mutation_active` serializes public mutations routed through
  one live filesystem instance, but `open_at` and `resolve_path` do not enter
  that serialization domain. No mount-generation contract currently proves
  that every live FAT access is routed through the same instance.
- `open_at` and `resolve_path` do not enter any mutation owner. They may read a
  directory entry before a concurrent replacement and return a handle after
  that replacement.
- The raw directory scan now has a bounded fail-closed validator for ordinal
  sequence, LAST, type/cluster-zero, alias checksum, canonical short-field
  padding, UTF-16 scalar structure, terminator/padding, and the 255-code-unit
  bound. This closes malformed-name lookup, but the decoded result still does
  not retain a serialized raw-chain digest for
  `Fat32ExecutableObjectObservationV1`.
- `fat32_executable_identity_observe_v1` has its own mutex. That mutex is not
  shared with the FAT directory/FAT mutation paths, so observing a dirent and
  publishing its identity are separate linearization domains.
- `FileHandle` contains a locator and cluster/size snapshot but no mount,
  object-generation, or reservation seal. It cannot detect replacement before
  later reads, and an output leaf cannot remain reserved across compiler
  creation/write/flush/rename.

## Required prerequisite

Introduce one non-copyable, mount-scoped FAT operation owner before adding the
adapter. It must:

1. own a mount-scoped BPB/mount generation and serialization authority shared
   by every live directory lookup, open, and mutation path for that mount;
2. make lookup/open/create/write/flush/unlink/rename/atomic-replace enter that
   same owner rather than consult an object-local boolean;
3. retain the validated raw LFN-chain/alias digest from the bounded directory
   validator inside the same serialized observation used for launch;
4. atomically read the validated LFN chain and 8.3 dirent, publish the
   executable identity, and acquire a generation-bound open handle while the
   owner remains held;
5. provide a bounded output-leaf reservation whose owner-consumed release or
   commit receipt prevents create/rename/replacement races and cannot be copied
   into a second authority;
6. invalidate affected object generations during every directory mutation and
   invalidate the mount generation before releasing the device on unmount;
7. quarantine the mount if lock release, identity publication, reservation
   commit, or mutation invalidation has an unknown outcome.

The executable loader must continue rejecting FAT32 launch inputs until an
exact live handle proves the same mount generation, directory locator, raw
dirent/LFN digest, and object generation at byte-read time. A compiler output
path additionally requires an active output-leaf reservation from absence or
expected replacement through durable publication.

## Rejected shortcut

A package-level helper that locks only around `resolve_path` plus
`fat32_executable_identity_observe_v1` was considered and rejected. Existing
mutation callers would not share that lock, output compilation spans multiple
calls, and the resulting snapshot would still be a time-of-check/time-of-use
claim rather than exact live proof.

## 2026-08-24 retry v2 outcome

A three-cycle static design/implementation retry was reverted in full without
running verification. It successfully explored raw validated LFN retention,
generation fields on `FileHandle`, mutation invalidation, and a bounded
output-leaf reservation, but the final review still found two mount-lifecycle
violations:

- filesystem operations entered the owner by `device_id`; after unmount and
  remount, a stale copied filesystem value could therefore join the newer
  generation while carrying stale geometry/cache state;
- mount mutated `bpb_parsed` and geometry before fallible recovery, root reads,
  and identity enrollment, with no already-mounted guard or transactional
  rollback. Double-mount and intermediate failure could strand a live seal or
  leave contradictory local state.

The next retry must make every begin/current/end operation consume the exact
instance seal (never device lookup), carry the exact operation receipt through
the call, reject double mount before state mutation, build mount state off-root,
and publish it only after recovery, root reads, and identity enrollment all
succeed. Every failure after enrollment must close that exact seal before
returning; an indeterminate close must quarantine and withdraw publication.

## 2026-08-24 retry v3 outcome

A lifecycle-only draft was independently rejected and reverted without running
verification. It confirmed that an exact slot/slot-generation/mount-generation
seal is necessary, but exposed additional requirements that must be designed as
one canonical transaction:

- generation publication and `g_fat32_mount_fs`/device publication cannot be
  separate state transitions; otherwise a published generation can leak when
  canonical publication fails, and concurrent publishers can overwrite;
- copied `Fat32Filesystem` values cannot receive close authority merely by
  carrying a copied exact seal; only a non-copyable canonical mount owner may
  invalidate the generation;
- candidate recovery currently publishes process-global atomic-replace
  capabilities, so it is not an isolated off-root transaction and can disturb
  an already-live mount;
- legacy test-created filesystems publish without a mounted identity, requiring
  an explicit test-only boundary rather than weakening production admission;
- capacity and identity-exhaustion behavior needs executable coverage.

The next design must therefore combine canonical filesystem/device publication,
generation state, replace-capability publication, and close authority under one
owner-side commit. A candidate may return only frozen state to that owner; it
must not mutate process globals or carry a caller-usable close operation.

## 2026-08-24 capsule-backed mount-owner prerequisite

`os.kernel.fs.fat32_capsule_mount_owner_v1` now supplies the missing coherent
transactional shape without changing production boot:

- one `BlockBackendIoLeaseV1` is the sole sector-I/O authority;
- BPB, root-cluster bytes, and replace capability are built off-root with
  bounded reads and no process-global mutation;
- filesystem state, mount generation, capability, and lease publish together;
- bounded generation/nonce operation receipts fence close and copied receipts
  become stale after owner-side release;
- close withdraws publication before consuming the capsule lease and
  quarantines an indeterminate release for exact retry.

This does not close the live-launch blocker yet. Legacy boot/syscall paths still
publish and retrieve copied `Fat32Filesystem` and `BlockDevice` values. The
side-effect-free candidate also truthfully publishes atomic replace as
unsupported until an owner-held journal replay transaction exists. Those
callers and recovery must migrate behind this mount owner's operation receipts
before executable identity can be bound to live reads.

The backend identity/capsule provider also needs a deterministic unpin-failure
injection seam before candidate-cleanup quarantine and exact retry can receive
executable failure-path coverage; the owner retains that authority today, but
this turn intentionally does not claim runtime evidence.
