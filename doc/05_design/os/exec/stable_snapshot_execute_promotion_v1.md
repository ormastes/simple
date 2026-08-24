# Stable snapshot execute promotion V1

## Purpose

MountTable can stream a bounded file through one retained backend handle. The
completion APIs let a hash consumer freeze that read phase and transfer the
same handle into executable admission. No promotion step resolves or reopens a
path, so a path replacement cannot redirect the already-selected object.

## Ownership and states

MountTable is the sole mutable owner. `StableFileSnapshotLeaseV1` is a bounded,
generational handle into its 1,024-row lease table. Snapshot bytes returned to
the hash consumer are owned copies. `StableFileSnapshotSealV1` is copyable,
immutable metadata and never authority.

The state sequence is:

`reading -> hash-tracking -> sealed -> promoted`, with close allowed before
promotion and invalid coverage/digest transitioning to close-only.

- `begin_stable_snapshot_promotion_hash_v1` explicitly opts a lease into hash
  tracking, so ordinary snapshot reads retain their prior cost. MountTable then
  hashes successful reads in its own allocation-bounded incremental
  SHA-256 state only while they cover the exact sequential range beginning at
  offset zero. A gap, overlap, out-of-order read, or unexpected short backend
  result permanently invalidates completion for that lease without changing
  ordinary read compatibility.
- `finish_stable_snapshot_v1` requires exact `[0,size)` coverage, computes the
  owner digest, and compares it with the consumer's canonical, nonzero
  lowercase SHA-256. It revalidates the live virtual handle and mount,
  namespace, and content generations before freezing reads. It does not close
  or consume the lease. Repeating the same finish is idempotent; attempting to
  replace its digest fails closed.
- The seal binds lease identity, mount identity, backend name and kind, all
  three generations, exact size, and the consumer digest.
- `promote_stable_snapshot_for_execute_v1` compares every seal field against
  owner state, revalidates the live virtual handle and current generations,
  applies mount execute capability, `noexec`, trust, and executable-size
  policy, then retires the lease and returns an `ExecuteOpenBinding` for the
  existing virtual handle. It makes no backend open or path-resolution call.
- Failed promotion retains the sealed lease so its owner may close it or retry
  after choosing an allowed trust policy. Successful promotion consumes it
  exactly once and deliberately does not close or unbind the transferred file
  handle. The execute binding becomes responsible for the eventual close.

## Failure and replay rules

Malformed/zero digests and premature finish are `InvalidArg`. Invalid stream
coverage or a consumer/owner digest mismatch is `Corrupt`. A forged or
digest-substituted seal is `Permission`. Missing, retired, recycled, or
generation-stale owner state is `StaleHandle`. Policy denial is `Permission`;
invalid executable size is `TooLarge`. Close remains valid exactly once in
reading, hash-tracking, sealed, or close-only state. A corrupt close-only lease
rejects later reads and finish attempts as `Corrupt`.
Promotion replay, close after promotion, and reads after finish all fail as
stale operations.

## Complexity and memory

Opted-in reads add O(chunk bytes) SHA-256 work; ordinary reads do not. One
state, block, schedule, and constant table is allocated per lease-table slot,
reset in place on reuse, and no full-file bytes are retained. Live and no-GC
lifetime hash memory are therefore O(lease-table slots). Incremental updates
complete at most one partial block, process complete 64-byte blocks directly,
and retain only the tail; helper dispatch and block-full checks are O(blocks),
not O(bytes), while byte work remains O(chunk bytes).

The compact mount list is reserved for path resolution. Every open file also
seals an index into a separate stable mount-slot registry. Snapshot read,
finish, promotion, close, and execute-current checks resolve that slot in O(1)
and centrally compare its never-reused MountId plus mount, namespace, and
content generations. Unmount clears its stable slot only after proving the
target has no live handles; later slot reuse cannot alias an old handle because
the MountId differs. Generation mutations update the compact entry and stable
slot atomically under the MountTable owner. Thus unrelated mount count no longer
multiplies sequential snapshot-read cost. Promotion also avoids
the path walk, backend open, stat, and associated handle allocation performed
by `open_for_execute`. The seal contains bounded scalar/text metadata.

FAT32 positioned reads transfer the already-owned request buffer directly when
the backend fills it. Only a short read allocates and copies an exact-size
prefix, avoiding the former second full-size allocation/copy on normal chunks.

## Focused coverage

`test/01_unit/lib/fs_driver/stable_file_snapshot_spec.spl` covers finish/read
exclusion, opt-in, premature/incomplete/unordered finish, owner digest mismatch,
idempotent finish, digest substitution, successful transfer, promotion and
close replay, forged backend metadata, untrusted policy denial, generation
invalidation, close-only corruption, a multi-chunk SHA-256 block boundary, and
close after failed promotion. It also covers direct full-block hashing and
stable mount identity across unrelated compact-list removal and stable-slot
reuse.
`test/01_unit/lib/common/crypto/sha256_stream_v1_spec.spl` locks partition
invariance for empty input, complementary partial blocks, full block plus tail,
multiple direct blocks, and mixed partial/direct-block updates.

This implementation was prepared under an explicit no-verification directive;
the focused coverage was added but not executed in this lane.
