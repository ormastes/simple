<!-- codex-architecture -->
# FAT32 recoverable atomic-replace owner for SimpleOS database roots

## Status and scope

Proposed design; no implementation or verified durability claim exists yet.
FAT32 does not natively provide atomic replace.  The existing
`Fat32Filesystem.rename_at` remains a non-atomic, no-replace namespace move.
This design adds a distinct filesystem-owned transaction protocol only for a
durable, same-volume replacement whose destination name already exists (or is
being created for the first committed generation).  Its initial policy is an
allowlist of SimpleOS root database files.  It is not a POSIX `rename` claim.

## Current-state findings

- `src/lib/nogc_sync_mut/database/atomic.spl` defines the canonical sequence:
  lock, write `<path>.tmp`, sync the temporary file, replace `<path>`, unlock.
- `src/os/kernel/fs/fat32.spl:rename_at` links the source at a new name and then
  deletes the old name.  It rejects an existing destination and explicitly
  documents the two directory writes as non-atomic.
- `Fat32Filesystem.mount` reads BPB/root state and `fat32_mount_publish`
  immediately exposes it; there is no pre-publication replace recovery.
- `fat32_fd_sync` writes file metadata and then calls `BlockDevice.flush`.
  The default block-device flush is an error, which is the correct fail-closed
  base contract.

## Decision

### One canonical mutation owner

`Fat32AtomicReplaceOwner` is the sole owner of journal state, directory-sector
images, FAT-chain reclamation, generation allocation, and mount recovery.
Callers transfer validated paths and an already-synced temporary-file handle;
they never mutate directory entries or FAT sectors concurrently.  The mount
owner must finish recovery before `fat32_mount_publish`.  Namespace lookup,
open, create, unlink, and ordinary rename are serialized against an active
replace by the same filesystem mutation lock.

The database keeps its existing `atomic_write` meaning.  A SimpleOS runtime
adapter maps only its final replace operation to this capability; it may set
`atomic_replace_rename` and `crash_recovery` true only after mount recovery and
device flush support succeed.

### Provisioned bounded journal

The disk image provisioner reserves a fixed, contiguous 16-sector journal
extent outside allocatable file clusters and records its LBA/length in a
SimpleOS FAT32 extension descriptor.  Mount validates that the extent is in
range, does not overlap BPB/FAT/root/data allocation, and has exactly two
8-sector banks.  Missing, overlapping, fragmented, wrong-sized, or
unflushable storage disables the capability.  Runtime never creates or grows
the journal and never trusts a discoverable ordinary file as authority.

Each bank contains one 512-byte header and seven payload sectors.  A record is
valid only when magic/version, bank index, monotonically ordered `u64`
generation (half-range comparison), state, entry count, every descriptor,
payload length, header CRC32C, and payload CRC32C validate.  The payload holds
at most four complete 512-byte post-operation directory-sector images.  Four
is sufficient for one destination alias sector plus a maximum FAT LFN+alias
source chain crossing at most three sectors; duplicate LBAs are coalesced.
The header also contains destination/source identity, new and old first
clusters and sizes, and reclamation `current`/`next` cluster cursors.  Paths
are not recovery authority.

Records are copy-on-write between banks: payload first, device flush, header
last, device flush.  A torn write makes the candidate invalid; recovery uses
the highest valid generation.  A terminal `DONE` record is itself a newer
valid record, so an older committed bank can never be replayed after cleanup.
No sector-write atomicity is assumed; checksummed redundant banks plus ordered
flush are required.

### Transaction and crash contract

After the caller has durably synced the temporary file:

1. Resolve and revalidate source/destination directory identities under the
   mutation lock.  Reject different volumes, directories, open conflicting
   writers, unbounded/corrupt LFN chains, aliased cluster ownership, and more
   than four distinct affected directory sectors.
2. Construct coalesced final sector images.  If source and destination share a
   sector, both the destination pointer/size update and source deletion appear
   in one image.  Otherwise all images are included in the same record.
3. Persist a newer `COMMITTED` record (payload, flush, header, flush).  No
   filesystem metadata may change before this point.
4. Write every recorded final directory-sector image in ascending LBA order,
   then flush.  Rewriting the same image is idempotent.  From this durability
   point the destination names the complete new chain and the temp name is
   absent; there is no durable state with the destination absent.
5. Persist `RECLAIM(current, next)` before freeing each old-chain cluster.
   Flush the record, free `current` in every FAT copy, flush, then advance.
   Recovery treats an already-free `current` as completed and continues from
   saved `next`.  It validates `next` before mutation and fails mount on a
   loop, cross-link, reserved/bad cluster, or ownership mismatch.
6. Persist a newer `DONE` record and flush.  Only then may the database call
   return success and release its lock.

Crash before a valid `COMMITTED` record leaves the namespace unchanged.  A
valid `COMMITTED` or `RECLAIM` record is always redone to the final images and
then reclaimed.  `DONE` requires no replay.  Recovery is idempotent across
arbitrarily repeated resets at every write/flush boundary.  Corrupt or
ambiguous newest state fails mount read-only/unavailable; it never guesses.

The old chain remains allocated until the new namespace state is durable.
The per-cluster cursor prevents unbounded leaked old generations during
repeated recovery.  At most the fixed 16 journal sectors plus the one old
generation currently being reclaimed are retained.

## Capability interface

The common contract is typed and does not alter `rename_at`:

```text
enum AtomicReplaceRecoveryLevel { Unsupported, RecoverableReplaceV1 }
struct AtomicReplaceRecoveryCaps {
    level, journal_bytes, max_dir_sectors, durable_flush,
    mount_recovery_complete, same_volume_only, root_db_policy
}
fat32_atomic_replace_caps() -> AtomicReplaceRecoveryCaps
fat32_atomic_replace(source_tmp, destination) -> Result<ReplaceReceipt, FsError>
fat32_atomic_replace_recover() -> Result<RecoveryReceipt, FsError>
```

Receipts contain journal generation, destination directory identity, old/new
first cluster, terminal state, flush count, and recovered/not-recovered.  They
contain no pointers or mutable filesystem objects.  `RecoverableReplaceV1` is
reported only after recovery completes and a real durable flush is available.

## Rejected alternatives

- Calling current `rename_at` atomic: contradicted by its implementation.
- Delete destination then rename temp: admits a durable missing destination.
- One marker file or one journal sector: a torn marker cannot distinguish
  intent from corruption without assuming sector atomicity.
- Logging paths only: lookup metadata may itself be torn or ambiguous.
- Clearing intent before old-chain reclamation: repeated crashes leak storage.
- Database-specific FAT writes: violates the filesystem mutation owner and
  forks canonical `atomic_write` semantics.

## Acceptance boundary

Capability promotion requires deterministic fault injection after every
sector write and flush, same-sector and different-sector cases, corrupt-bank
selection, repeated-recovery convergence, bounded-space proof, and a fresh
QEMU boot reading the acknowledged generation through the public DB protocol.
A second in-memory read, serial marker, or host-edited image is not evidence.
