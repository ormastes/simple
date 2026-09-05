<!-- codex-design -->
# Detail design: FAT32 recoverable database-root replacement

## On-disk record V1

The provisioned journal is two banks of eight 512-byte sectors.  Integers are
little-endian.  Header fields are: magic `SARJ`, version `1`, bank, state
(`COMMITTED`, `RECLAIM`, `DONE`), generation, header length, payload length,
image count (0..4), destination parent cluster/dirent LBA/offset, source parent
cluster/alias LBA/offset/LFN slot count, old/new first cluster and byte size,
reclaim current/next, four `(lba, payload_offset, crc32c)` descriptors, payload
CRC32C, and header CRC32C with its own field zeroed.  Unused bytes must be zero.

Payload sectors contain complete final 512-byte directory sectors, not patches.
Descriptors are strictly increasing by LBA, non-overlapping, sector-aligned,
and each image has its own CRC.  Source deletion includes all validated LFN
slots.  Destination keeps its name/attributes and changes only cluster/size
fields; creation of the first destination uses a pre-reserved destination slot
set and obeys the same four-sector bound.

## Owner algorithm

`prepare_replace` resolves both names twice (before and after locking), proves
the temp file owns the new chain exclusively, proves the destination owns the
old chain exclusively, snapshots affected sectors, applies changes to copies,
coalesces by LBA, and validates the final images by parsing them before I/O.
No mutation occurs if preparation fails.

`publish_record(record)` writes the inactive bank's payload sectors, flushes,
writes its header, flushes, rereads and validates the bank, then adopts its
generation in memory.  Flush false/error and reread mismatch are fatal.

`apply_images(record)` rereads each current sector only for diagnostics, writes
the recorded whole-sector image, then flushes once after the ordered batch.
The same-sector case therefore performs one directory-sector write.  The
different-sector case may expose old or new content to a concurrent raw disk
reader, but filesystem namespace readers are excluded by the mutation lock;
after any reset, pre-publication recovery converges to new.

`reclaim_old_chain(record)` reads the next FAT value before each free.  It
publishes `RECLAIM(current, next)` before altering FAT.  If `current` is
already free, it advances using saved `next`; if allocated, its observed next
must equal saved `next`.  Every FAT copy is updated and flushed before the next
cursor record.  End-of-chain publishes `DONE`.  The new chain and journal
extent are forbidden reclamation targets.

`recover_before_publish` validates both banks independently and chooses the
highest valid generation.  No valid bank means a pristine provisioned journal
only if both headers are all-zero; otherwise capability/mount fails.  DONE is
a no-op.  COMMITTED reapplies images then reclaims.  RECLAIM first reapplies
images, then resumes the cursor.  Recovery must finish before root-dir cache is
loaded or must reload it afterward; publishing a cache assembled before replay
is forbidden.

## Errors and policy

- `Unsupported`: no valid provisioned extent or no durable device flush.
- `Invalid`: malformed record, LBA overlap/range error, generation ambiguity.
- `Conflict`: identity changed after locking, cross-linked/open chain, source
  is not the expected synced temp, destination policy mismatch.
- `TooLarge`: more than four affected directory sectors.
- `Io`: any write, flush, or verify-read failure.
- `NeedsRepair`: FAT loop, bad/reserved cluster, ownership mismatch.

All errors are fail-closed.  No fallback invokes `rename_at`, delete+rename,
or reports database readiness.  Initial allowlist is exact normalized root DB
paths selected by the server capsule; traversal, subdirectories, directory
replacement, cross-volume operation, batches, and generic application files
are rejected.

## Exact executable-spec handoff

Create `test/01_unit/os/kernel/fs/fat32_atomic_replace_recovery_spec.spl` with
helpers `Given_provisioned_replace_journal`, `When_replace_crashes_after`,
`When_mount_recovery_runs`, and `Then_exactly_generation_is_visible`.

- `FAR-001`: source/destination in one directory sector produces one coalesced
  final image; crash at every write/flush boundary recovers exactly new.
- `FAR-002`: source and destination in different sectors/directories produces
  ordered distinct images; every crash point recovers exactly new after valid
  COMMITTED, and exactly old before it.
- `FAR-003`: corrupt/torn newest header, payload, and individual image selects
  the older valid bank; two invalid nonzero banks fail closed.
- `FAR-004`: reset recovery repeatedly at every replay/reclaim boundary;
  convergence is identical and no cluster is double-freed or cross-freed.
- `FAR-005`: old chain lengths 0, 1, and many are fully reclaimed using the
  durable cursor; journal use remains exactly 16 sectors.
- `FAR-006`: missing journal, unsupported/error/false flush, out-of-range LBA,
  generation ambiguity, FAT loop/bad cluster, cross-link, >4 sectors,
  different volume, directory target, and unapproved path all fail closed.
- `FAR-007`: `DONE` outranks an older COMMITTED bank and never replays it.
- `FAR-008`: mount never calls `fat32_mount_publish` or exposes stale
  `root_dir_data` before successful recovery.
- `FAR-009`: ordinary `rename_at` remains explicitly non-atomic and its caps
  remain distinct from `RecoverableReplaceV1`.

Create `test/03_system/os/server/fat32_database_replace_reboot_spec.spl` with
manual steps `Given a writable provisioned FAT32 server image`, `When the DB
commit is power-cut at crash point N`, `When the same image boots again`, and
`Then the public DB protocol returns exactly the acknowledged generation`.
Run every protocol crash point, preserve serial/disk/protocol receipts, require
a new QEMU process, and include a negative unprovisioned-image scenario.

No placeholder may satisfy a requirement.  Unimplemented crash injection or
fresh-boot checking must remain `fail(...)`, never `expect(true)`.
