# FAT32 capsule mount owner v1

## Decision

The canonical mount is a single mutex-owned tuple: mounted filesystem state,
mount generation, atomic-replace capability, authenticated backend lease, and
bounded operation table. `BlockBackendIoLeaseV1` is the sole sector-I/O
authority. A copied `BlockDevice` is never published.

## Transaction

1. Reject an already-active mount before acquiring storage authority.
2. Acquire one pin-coupled backend lease.
3. Read and validate the BPB, root cluster, and replace descriptor into a
   bounded off-root candidate. Candidate discovery performs no writes and
   changes no process-global capability. Admission requires the FAT32 cluster
   count range and proves that the declared FAT has a 32-bit entry for every
   data cluster plus its two reserved entries.
4. Commit the filesystem, generation, capability, and backend lease together
   under the mount-owner mutex. A racing publisher loses admission before it
   acquires storage authority.
5. Admit I/O only with a generation/nonce-bound operation receipt. The bounded
   owner slot, rather than the copyable receipt, is authoritative.
6. Close rejects while operations remain. It withdraws filesystem and
   capability publication first, then consumes the capsule lease. An uncertain
   release quarantines the mount for exact retry. Candidate rollback has a
   separate quarantine discriminator and retains both its lease and exact
   capsule seal; it cannot be retried through the mounted-close path.

## Bounds and complexity

- At most 128 root sectors (the FAT32 sectors-per-cluster maximum) are retained.
- At most 64 concurrent operation slots exist. Admission is O(64) worst case;
  dispatch is O(1), and no full-tree lookup or backend copy occurs per I/O.
- Candidate memory is bounded to 64 KiB root data plus two 512-byte sectors.

## Capability truth

V1 candidate discovery is deliberately side-effect-free and therefore does not
claim journal recovery. Its atomically published replace capability remains
`Unsupported`. Promotion to `RecoverableReplaceV1` requires a separate,
owner-held recovery transaction that durably replays the journal before the
same publication commit.

## Remaining integration boundary

Legacy `fat32_mount_publish` and syscall adapters still expose copied
`Fat32Filesystem`/`BlockDevice` values. Production boot must migrate those
callers to mount operation receipts before this owner can replace the legacy
global. Until then this module is a coherent authority prerequisite, not a
claim that live filesystem launch is complete.
