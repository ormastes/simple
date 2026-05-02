# NVFS (SimpleFS-NV) Design — Version 2

> **Supersedes:** `doc/05_design/nvfs_design.md` (v1). The v1 document is preserved for
> historical reference; its header has been updated to point here. All new work should
> reference this document.
>
> **Related designs (cross-refs):**
> - `doc/05_design/fs_driver_interface.md` — shared SimpleOS FS driver interface; NVFS
>   implements `DriverInstance::Nvfs` and `DriverInstance::NvfsPosix`.
> - `doc/05_design/nvfs_posix_wrapper.md` — POSIX-over-NVFS compat shim design.
> - `doc/05_design/nvfs/svllm_requirements.md` — svllm client requirements (R1–R9).
> - `doc/05_design/nvfs/from_spostgre.md` — spostgre engine contributions (S1–S7).
> - `doc/05_design/spostgre_design.md` — spostgre engine design.
>
> **Status:** Phase 9-extend design deliverable (2026-04-18).

---

## 1. Scope delta vs v1

Version 1 established the core NVFS model: virtual storage classes, the `arena_*` API,
superblock + checkpoint ring, ZNS/FDP optional paths, and milestones N1–N5. It did not
address Merkle-tree integrity, birth-generation tracking, extent back-references,
snapshots+subvolumes, block cloning, deduplication, send/receive, native encryption,
per-chunk RAID, ARC caching, or a POSIX compat wrapper.

v2 incorporates all five Btrfs headline features and all five ZFS headline features from
the Phase 9 research documents, integrates the shared FS driver interface design, and
adds three new milestones (N6–N8). The on-disk layout is extended: the pmap entry widens
from 40 bytes to 80 bytes to carry birth generation + checksum.

| Change area | v1 | v2 |
|---|---|---|
| pmap entry | 40 bytes | 80 bytes (+birth_gen +checksum +algo) |
| B-tree forest | pmap + WAL + checkpoint | 10-tree forest (see §2) |
| Integrity | implicit CRC on WAL | Merkle parent-stores-child (§3) |
| Birth tracking | none | 8 bytes per pointer (§4) |
| Extent back-refs | none | 4 variants (§5) |
| Snapshots | not designed | tree-sharing + ref-increment (§6) |
| Block cloning | `arena_clone_range` stub | full reflink syscall (§7) |
| Dedup | none | offline background job (§8) |
| Self-healing | none | mirror consult + scrub (§9) |
| Send/receive | none | TLV stream + incremental (§10) |
| Backup roots | 1 superblock copy | 4 backup_tree_root entries (§11) |
| RAID | single global | per-chunk/per-arena profile (§12) |
| Cache | OS page cache | ARC MRU+MFU+ghosts (§13) |
| Encryption | none | 3-level key hierarchy (§14) |
| Block-group tree | extents carry group items | isolated tree (§15) |
| Milestones | N1–N5 | N1–N8 (N6–N8 are new) |

---

## 2. Shadowed-CoW B-tree forest

**Source:** Btrfs research §2.2, §2.3; NVFS translation §16.1.

NVFS stores all metadata in a forest of copy-on-write B-trees. The key insight from
Rodeh 2008 is that shadowing — allocating a new node on every write and updating the
parent to point at it — naturally chains into an atomic commit when the superblock CAS
fires. NVFS extends this to ten tree types.

### 2.1 Tree catalogue

| Tree | Objectid constant | Purpose |
|---|---|---|
| Root tree | `ROOT_TREE_OBJECTID = 1` | Roots of all other trees; one ROOT_ITEM per tree |
| Extent tree | `EXTENT_TREE_OBJECTID = 2` | Allocator book; every non-free logical extent |
| Chunk tree | `CHUNK_TREE_OBJECTID = 3` | Logical↔physical map; one CHUNK_ITEM per arena chunk |
| Device tree | `DEV_TREE_OBJECTID = 4` | Physical↔logical inverse; walked by device remove/replace |
| FS tree | `FS_TREE_OBJECTID = 5` | One per subvolume; INODE_ITEM + DIR_ITEM + EXTENT_DATA |
| Checksum tree | `CSUM_TREE_OBJECTID = 7` | Per-block checksums for data extents |
| Reflink tree | `REFLINK_TREE_OBJECTID = 8` | Back-refs for shared extents (reflink + dedup) |
| Log tree | `LOG_TREE_OBJECTID = 9` | Intent log for fsync-without-commit |
| Block-group tree | `BLOCKGROUP_TREE_OBJECTID = 11` | BLOCK_GROUP_ITEMs isolated for fast mount |
| Free-space tree | `FREE_SPACE_TREE_OBJECTID = 10` | Free extents; replaces v1 free-extent bitmap |

### 2.2 Key / item format

Every item in every tree is addressed by a 136-bit compound key:

```
struct NvfsKey:
    objectid: u64   # what you are talking about (inode id, bytenr, chunk_offset, …)
    item_type: u8   # INODE_ITEM, EXTENT_DATA, CHUNK_ITEM, TREE_BLOCK_REF, …
    offset: u64     # subkey within the objectid's namespace
```

Keys are sorted lexicographically `(objectid, item_type, offset)`. This sortability
enables range scans of per-object metadata (e.g., all EXTENT_DATA items for inode 42).

### 2.3 Node layout

Every internal node and leaf carries:

```
struct NvfsNodeHeader:
    checksum: [u8; 32]   # Merkle checksum over the rest of this node (see §3)
    fsid: [u8; 16]       # filesystem UUID
    bytenr: u64          # expected LBA; verifies node is at the right location
    flags: u64           # WRITTEN | RELOC | …
    chunk_tree_uuid: [u8; 16]
    generation: u64      # transaction generation when this node was written
    owner: u64           # objectid of the tree that owns this node
    nritems: u32
    level: u8            # 0 = leaf
```

`generation` is a monotonically increasing counter incremented once per transaction
commit. It enables all birth-generation features (§4) at the node level.

---

## 3. Merkle parent-stores-child checksums

**Source:** ZFS research §2.6, §3.3; ZFS NVFS translation table §16.

Every pointer in the NVFS tree forest stores a checksum of its target. This is the ZFS
"parent-stores-child" Merkle model: corruption is detected on first access, not on a
separate fsck pass. The chain of checksums forms a Merkle tree rooted at the superblock.

### 3.1 Extended pmap entry

The pmap entry widens by 41 bytes to carry birth generation, checksum algorithm tag, and
the checksum itself:

```
offset  size  field
0x00    8     logical_page_no (u64)
0x08    8     physical_arena_id (u64)
0x10    8     physical_offset (u64)
0x18    8     page_generation (u64)       # CoW generation (v1 field, retained)
0x20    8     birth_gen (u64)             # NEW: txg when this pointer was born (§4)
0x28    1     checksum_algo (u8)          # NEW: algorithm tag (see §3.2)
0x29    3     reserved_algo_pad
0x2C    4     flags (u32)                 # bit0=blob_pointer, bit1=evicted (v1 bits retained)
0x30    32    checksum (u8[32])           # NEW: checksum of target block
```

Total: 80 bytes (v1 was 40 bytes).

The 32-byte checksum field is wide enough for blake3-256. Shorter algorithms (CRC32C = 4
bytes, xxhash = 8 bytes) left-pad with zeros. The `checksum_algo` tag tells the reader
which slice to interpret.

### 3.2 Checksum algorithm enum

```
enum ChecksumAlgo:
    CRC32C   = 0   # 4 bytes used; fast, adequate for accidental corruption
    XXHash64 = 1   # 8 bytes used; fast, good non-crypto hash
    SHA256   = 2   # 32 bytes used; cryptographic; required for raw-send auth
    Blake3   = 3   # 32 bytes used; default for new volumes; SIMD-friendly
```

Default for new volumes: `Blake3`. Per-volume choice recorded in superblock
`default_csum_algo` field. Per-extent override supported (for mixed-algo pools during
migration).

### 3.3 Checksum verification on read

On every block read: compute checksum of block bytes, compare with the checksum stored in
the parent pointer. Mismatch → `FsError::Corrupt` → trigger self-healing (§9). The
verification happens inside the NVFS read path, before the data is returned to the
caller. Callers cannot bypass it.

---

## 4. Birth-generation on every pointer

**Source:** ZFS research §2.6 (`birth txg` field in blkptr_t), §6.3 (dead lists).

Every pointer in the NVFS tree forest carries a `birth_gen` field (8 bytes): the
transaction generation in which this pointer was first written. Pointer copies (reflinks,
snapshots) inherit the origin's birth_gen — they were not "born" in the copy transaction.

**What this enables:**

| Feature | Mechanism |
|---|---|
| O(1) incremental send | Prune all pointers with `birth_gen <= from_snapshot_gen` |
| Cheap snapshot deletion (dead lists) | Collect pointers with `birth_gen > parent_snap_gen` |
| Scrub pruning | Skip blocks born in a prior, already-verified scrub cycle |
| CoW audit | Every block can be traced to the transaction that created it |

**Space cost:** 8 bytes per pointer. In a tree with a branching factor of 128, a 1 TiB
filesystem has roughly 10 million leaf pointers + 80,000 internal pointers. Cost:
~80 MiB for birth_gen fields across all live pointers — acceptable.

The pmap entry layout in §3.1 allocates `offset 0x20` for `birth_gen`.

---

## 5. Extent back-references

**Source:** Btrfs research §2.6, §5.1, §16.1 (extent backrefs section).

The extent tree records every non-free logical extent plus back-references (backrefs)
from that extent to the fs-tree ref(s) that own it. NVFS adopts four backref variants
matching Btrfs's skinny_metadata layout:

| Type constant | Key form | Meaning |
|---|---|---|
| `TREE_BLOCK_REF = 176` | `(bytenr, TREE_BLOCK_REF, tree_id)` | Metadata block owned by a specific tree |
| `SHARED_BLOCK_REF = 182` | `(bytenr, SHARED_BLOCK_REF, parent_bytenr)` | Metadata block shared (snapshot) via parent pointer |
| `EXTENT_DATA_REF = 178` | `(bytenr, EXTENT_DATA_REF, hash(root+obj+off))` | Data extent owned by a specific inode+offset |
| `SHARED_DATA_REF = 184` | `(bytenr, SHARED_DATA_REF, parent_bytenr)` | Data extent shared (reflink/snapshot) via parent pointer |

**What backrefs enable:**

- **Cheap snapshot deletion:** The dead-list calculation for a snapshot is: for each
  extent whose last backreference is the deleted snapshot, free the extent.
- **Scrub-driven repair:** Given a corrupt data block (bytenr), walk the
  EXTENT_DATA_REF / SHARED_DATA_REF items to find the owning inode and log a repair
  note to the operator.
- **Fsck:** Offline `nvfs check` can verify the reference graph is consistent without
  walking the entire fs tree.

Delayed ref flushing (a.k.a. delayed backrefs): backref updates are batched in an
in-memory queue and flushed to the extent tree at transaction commit time. This is the
same design as Btrfs's `delayed_ref` machinery. It is a known bug-attractor; NVFS must
ship comprehensive tests for queue ordering and crash consistency before shipping N4.

---

## 6. Snapshots and subvolumes

Subvolumes are independent FS trees sharing the same chunk/extent/device trees. Each
subvolume has a ROOT_ITEM in the root tree pointing at its FS-tree root.

**Snapshot creation** (O(1)):
1. Increment the refcount on the source subvolume's FS-tree root block.
2. Write a new ROOT_ITEM for the snapshot pointing at the same root block.
3. Commit the transaction.

On the next write inside the source subvolume, CoW diverges the FS tree: the written
node is allocated fresh, its parent is rewritten, and the chain ripples up to a new root.
The snapshot's root remains pointing at the pre-write version.

**Writable clones:** same as read-only snapshot creation, but the clone's ROOT_ITEM
carries a `writable` flag. Writers CoW inside the clone's tree; the source is
unaffected. The SHARED_BLOCK_REF mechanism tracks which blocks are still shared.

**Subvolume deletion:** requires collecting all extents whose last backref points only to
the deleted subvolume (the dead list). Requires traversing the subvolume's FS tree.
Birth-gen (§4) and dead lists make this O(dead_extents) rather than O(total_extents).

---

## 7. Block cloning and reflink

**Source:** ZFS research §7 (block cloning in OpenZFS 2.2), NVFS v1 `arena_clone_range`.

`arena_clone_range` already exists in the v1 API. v2 extends it to a user-visible reflink
operation that works at file-system granularity.

**Mechanism:**

1. Caller issues `nvfs_reflink(src_fd, src_off, dst_fd, dst_off, len)`.
2. NVFS looks up the EXTENT_DATA items in the source inode covering `[src_off, src_off+len)`.
3. For each source extent, NVFS:
   a. Adds a SHARED_DATA_REF backref to the extent tree (refcount++).
   b. Writes an EXTENT_DATA item in the destination inode pointing at the same physical extent (with the source extent's birth_gen preserved).
4. Commits the transaction.

**No DDT (Deduplication Table):** Block cloning is an explicit, user-triggered operation
(via syscall or `cp --reflink=always`). There is no inline RAM-resident hash table that
taxes every write. Deduplication (§8) is a separate offline job.

**Copy-on-write on first write:** When the destination inode's file data is written, the
shared extent is CoW'd: a new extent is allocated, the data is copied+modified, the
backref to the old extent is decremented, and the new extent gets a fresh backref.

---

## 8. Offline deduplication

**Source:** Btrfs research §16 (duperemove/bees-equivalent offline dedup).

Inline dedup (hashing every write and checking a global DDT) is **explicitly not in scope
for NVFS v2**. The memory cost and write-path latency are unacceptable for NVMe workloads
where the write path must be latency-predictable.

**Offline dedup:** a background daemon (comparable to `duperemove` or `bees` on Btrfs)
runs when the filesystem is idle:

1. Scan data extents in the checksum tree.
2. For extents with matching checksums, verify byte-for-byte equality (to guard against
   checksum collisions with weak algorithms).
3. Issue `nvfs_reflink_extent_same(arena_a, off_a, arena_b, off_b, len)` — the NVFS
   equivalent of the Linux `FIDEDUPERANGE` ioctl — to deduplicate the matching extents.
4. The reflink machinery (§7) handles the backref updates.

The offline dedup daemon is a userspace process; it does not require kernel changes. It
is **capability-gated**: `Capability::Dedup` is advertised by NVFS-native mounts; the
daemon queries this before proceeding.

---

## 9. Self-healing

On a checksum mismatch detected during a read (§3.3):

1. Check if a mirror or replica exists for the arena chunk (per-chunk RAID profile §12).
2. If yes: read the same logical block from the mirror. Verify its checksum.
3. If the mirror's checksum is good: rewrite the bad block from the mirror's copy
   (`arena_clone_range` at the physical level). Log the repair to the operator.
4. If no mirror is available, or the mirror is also corrupt: return `FsError::Corrupt`
   to the caller. Log the damage extent (bytenr + owning inode via backrefs §5).

**Scrub background job:** walks the entire checksum tree and verifies every data extent.
On mismatch, triggers the repair procedure above. Scrub is throttled to avoid saturating
the NVMe device during normal operation. Birth-gen (§4) enables scrub pruning: extents
born after the last successful scrub can be skipped on incremental scrub runs.

---

## 10. Send and receive

**Source:** ZFS research §9; Btrfs research §16 (send/receive).

`nvfs send` produces a TLV byte stream encoding a snapshot's content. `nvfs receive`
replays that stream to reconstruct the snapshot on a target volume.

### 10.1 Stream format

```
stream := stream_header TLV* stream_end
TLV    := type (u32) + length (u32) + value (bytes)

TLV types:
  SUBVOL    - name, UUID, generation
  SNAPSHOT  - name, parent UUID, generation
  MKFILE    - path
  MKDIR     - path
  WRITE     - path, offset, data
  CLONE     - src_path, src_off, dst_path, dst_off, len (reflink-optimized)
  RENAME    - old_path, new_path
  UNLINK    - path
  SET_XATTR - path, name, value
  TRUNCATE  - path, size
  CHOWN     - path, uid, gid
  CHMOD     - path, mode
  UTIMES    - path, atime, mtime
  END       - fletcher4 over entire stream
```

### 10.2 Incremental send

`nvfs send --parent <snap> <snap2>` prunes all pointers with `birth_gen <= parent_snap_gen`.
Only blocks born after the parent snapshot are emitted. This is O(changed_extents) not
O(total_extents), made possible by birth-gen (§4).

### 10.3 Encrypted raw send

When the source filesystem uses native encryption (§14): `nvfs send --raw` emits
ciphertext bytes without decrypting. The receiver stores the encrypted ciphertext as-is.
The target does not need the decryption key; it only stores encrypted blocks. The IV and
auth tag are included in the stream alongside ciphertext so the receiver can verify
integrity without decrypting.

---

## 11. Backup roots in superblock

**Source:** Btrfs research §10.6 (`backup_tree_root` array), §14.1 (`usebackuproot`
mount option).

The NVFS superblock carries four `backup_tree_root` entries alongside the primary root
pointer. Each entry is written at the close of a transaction commit (round-robin across
the four slots). On mount, if the primary root pointer is unreadable or its checksum
fails, NVFS tries the backup roots in reverse-generation order.

```
struct NvfsSuperblock:
    magic: [u8; 8]                # b"NVFS0002"
    fsid: [u8; 16]
    bytenr: u64
    generation: u64
    root_tree_lba: u64            # primary root tree root
    root_tree_gen: u64
    default_csum_algo: u8
    # ... other fields ...
    backup_roots: [BackupRoot; 4]

struct BackupRoot:
    root_tree_lba: u64
    root_tree_gen: u64
    chunk_root_lba: u64
    chunk_root_gen: u64
    timestamp_ns: u64
    crc32c: u32
```

**Mount option `rescue=usebackuproot`:** instructs the mount path to skip the primary
root and try backup roots immediately. Useful when the primary is corrupt but the drive
is otherwise readable.

The checkpoint ring (v1 §5.2) is complementary: backup roots give access to prior
committed generations; the checkpoint ring points at the intent log tail for recovery.
Together they give two layers of resilience against superblock or root corruption.

---

## 12. Per-chunk RAID profile

**Source:** Btrfs research §4, §13 (per-block-group RAID, balance/convert).

NVFS's v1 concept of per-class arena segments maps onto Btrfs's per-chunk RAID model.
Each arena chunk carries a `raid_profile` field in its CHUNK_ITEM:

```
enum RaidProfile:
    Single      # no redundancy
    Dup         # 2 copies on same device (protection vs silent bit-rot only)
    Mirror2     # 2 copies across 2 devices (replaces ambiguous "RAID1")
    Mirror3     # 3 copies across 3 devices
    Mirror4     # 4 copies across 4 devices
```

Note: RAID5/6 is **skip for v2**. The write hole (partial-stripe failure between data
and parity writes) is a real data-loss event. NVFS will not ship parity RAID until a
stripe journal or zoned-device alignment solution is designed.

**Storage class defaults:**

| NVFS class | Default profile |
|---|---|
| `META_DURABLE` | Mirror3 minimum |
| `DB_WAL` | Mirror2 minimum |
| `MODEL_IMMUTABLE` | Single (immutable after seal; integrity via checksum) |
| `GENERAL_MUTABLE` | Mirror2 |
| `DB_TEMP` | Single |

**Online balance / convert:** `nvfs balance convert=mirror2 --class=GENERAL_MUTABLE`
rewrites all GENERAL_MUTABLE arena chunks from their current profile to Mirror2. The
balance job reads chunks, rewrites them under the new profile, updates CHUNK_ITEMs in
the chunk tree, and commits. Normal I/O continues during balance; the balance job holds
a read-lock on the old chunk while rewriting.

---

## 13. ARC-like cache

**Source:** ZFS research §11 (ARC — Adaptive Replacement Cache, Megiddo+Modha FAST '03).

NVFS is a user-space daemon. It owns its block cache entirely — there is no kernel
page-cache duplication problem (unlike ZFS-on-Linux which fights the VFS page cache).

### 13.1 Four-queue design

```
ARC queues:
  MRU         - recently used once (likely sequential access)
  MFU         - frequently used (repeated access, likely hot metadata)
  MRU-ghost   - evicted from MRU (fingerprints only; no data)
  MFU-ghost   - evicted from MFU (fingerprints only; no data)

Cache size: arc_c (target), arc_c_max (hard cap), arc_c_min (floor).
p parameter: fraction of arc_c allocated to MRU; adapts on hit/miss.
```

**Eviction:** When the cache is full and a miss arrives, the adaptive `p` parameter
determines whether to evict from MRU or MFU. Ghost-list hits adjust `p`: MRU-ghost hit
→ increase MRU fraction (sequential workload); MFU-ghost hit → increase MFU fraction
(repeated-access workload).

### 13.2 NVFS-specific tuning

- Default `arc_c_max`: 25% of process RSS limit (not 50% of system RAM — NVFS is a
  user-space daemon sharing the machine with other processes).
- Metadata is always MFU-preferred (B-tree internal nodes are hot).
- Compressed cache: compressed blocks cached if compression is enabled (saves RAM).
- svllm tensor-pack objects (`MODEL_IMMUTABLE` class): pinned via `R6`
  `fs_register_buffer` — never evicted from cache while pinned.

---

## 14. Native encryption

**Source:** ZFS research §13 (native encryption AES-GCM, key hierarchy, raw send).

Encryption is **capability-gated** (`Capability::Encrypt`). It is off by default on new
volumes. When enabled:

### 14.1 Three-level key hierarchy

```
User key (passphrase or wrapped key from key manager)
  → wrapping key (per-volume, stored on disk)
    → master key (per-dataset, stored encrypted with wrapping key)
      → per-block data key (derived from master key + block address + IV)
```

`nvfs change-key` rewraps the master key with a new user key; it does not re-encrypt
data. Full re-encryption requires rewriting all data extents (expensive, offline).

### 14.2 Algorithm

`AES-256-GCM` is the default. `ChaCha20-Poly1305` is an optional alternative for
platforms without AES hardware acceleration.

### 14.3 IV management

96-bit IV derived deterministically from `{master_key_id, object_id, block_offset}`.
This determinism is required for raw send (§10.3): the same ciphertext on source and
target must have the same IV so the receiver can verify the auth tag.

### 14.4 What is not encrypted

Block pointers (pmap entries), checksums, and birth_gen fields are stored in plaintext.
An attacker with disk access can observe the Merkle structure and file sizes but not
block content. This matches ZFS's documented threat model.

---

## 15. Block-group tree split

**Source:** Btrfs research §2.5 (block-group tree, kernel 6.1+ incompat feature).

Before v2, NVFS would interleave BLOCK_GROUP_ITEM metadata with extent allocator records.
This forces mount-time scanning of the entire extent tree to find all block groups —
O(extents) mount time.

v2 ships the block-group tree (`BLOCKGROUP_TREE_OBJECTID = 11`) from day one. All
`BLOCK_GROUP_ITEM` records live exclusively in this tree. Mount needs only to read
the block-group tree root (one seek, O(block_groups) reads) rather than scanning
the full extent tree.

**Why ship from day one:** retrofit is painful (requires a one-time migration of all
BLOCK_GROUP_ITEMs from the extent tree to the new tree, plus an incompat flag). Starting
clean is cheaper. The block-group tree is small (one entry per arena chunk) and adds
minimal complexity.

---

## 16. Integrity checks

### 16.1 `nvfs check` (offline)

Unmounted filesystem integrity check. Walks the entire B-tree forest, verifies:
- Every node checksum matches its parent's stored checksum (Merkle, §3).
- Every extent backref is consistent with the fs-tree's EXTENT_DATA items (§5).
- Every allocated extent is reachable from at least one fs-tree.
- The free-space tree is consistent with the extent tree's holes.

Comparable to `btrfs check --readonly`.

### 16.2 `nvfs rescue`

Mounted (read-only) rescue mode. On mount failure:
1. Try backup roots in reverse-generation order (§11).
2. Replay the intent log (log tree, `LOG_TREE_OBJECTID = 9`) from the last valid
   checkpoint ring entry.
3. If log replay fails, offer `--usebackuproot=N` to select a specific backup root.

Comparable to `btrfs rescue + mount -o rescue=usebackuproot`.

### 16.3 Scrub (online)

Background job running while the filesystem is mounted:
1. Walk the checksum tree (not the entire fs tree).
2. For each data extent: read block, verify checksum against checksum-tree entry.
3. On mismatch: trigger self-healing (§9).
4. Record scrub progress in a persistent scrub-status object (survives crash-restart).

Birth-gen pruning (§4): extents born after the last successful full-scrub cycle are
skipped on the next incremental scrub, reducing redundant work.

---

## 17. Updated on-disk layout

### 17.1 Superblock (primary, at LBA 64)

```
offset  size  field
0x00    8     magic = b"NVFS0002"
0x08    16    fsid (UUID)
0x18    8     bytenr (expected LBA, self-referential)
0x20    8     generation (u64)
0x28    8     root_tree_lba (u64)
0x30    8     root_tree_gen (u64)
0x38    8     chunk_root_lba (u64)
0x40    8     chunk_root_gen (u64)
0x48    8     log_root_lba (u64)
0x50    8     log_root_gen (u64)
0x58    8     blockgroup_root_lba (u64)  # NEW: block-group tree root
0x60    8     blockgroup_root_gen (u64)  # NEW
0x68    1     default_csum_algo (u8)     # NEW: ChecksumAlgo enum
0x69    1     encrypt_enabled (u8)       # NEW: 0=off, 1=on
0x6A    6     reserved_flags
0x70    8     total_bytes (u64)
0x78    8     bytes_used (u64)
0x80    16    label (UTF-8, null-padded)
# ... incompat_flags, compat_ro_flags ...
0x140   (4 * 48)  backup_roots[4]       # NEW: BackupRoot array (§11)
0x200   32    superblock_csum (blake3)   # NEW: checksum of superblock itself
0x220   (pad to 4096)
```

### 17.2 Pmap entry (v2, 80 bytes)

```
offset  size  field
0x00    8     logical_page_no (u64)
0x08    8     physical_arena_id (u64)
0x10    8     physical_offset (u64)
0x18    8     page_generation (u64)      # CoW generation (v1 retained)
0x20    8     birth_gen (u64)            # NEW: txg of first write (§4)
0x28    1     checksum_algo (u8)         # NEW: ChecksumAlgo tag (§3.2)
0x29    3     reserved_algo_pad
0x2C    4     flags (u32)                # bit0=blob_pointer, bit1=evicted (v1 bits)
0x30    32    checksum (u8[32])          # NEW: Merkle checksum of target (§3)
```

Total: 80 bytes. The 40-byte v1 entry is not forward-compatible; v2 uses magic
`b"NVFS0002"` to distinguish from v1's `b"NVFS0001"`. Migration: offline tool reads v1,
computes checksums for all extents, writes v2 superblock with new magic.

---

## 18. Phased milestones

Milestones N1–N5 are updated from v1 with the new capabilities. N6–N8 are new.

### N1 — Core append-only storage (4 weeks, 1 eng)

- Superblock v2 (magic `NVFS0002`, backup_roots array, default_csum_algo field).
- Checkpoint ring + intent log.
- Block-group tree from day one (§15).
- `arena_create`, `arena_append`, `arena_seal`, `arena_discard`, `arena_read`,
  `arena_readv`.
- CRC32C checksum on all data blocks (Merkle level 1 only — pmap entry checksum).
- Birth-gen field in pmap entry (populated, not yet consumed by features).

**Acceptance:**
- Mount/unmount cycle preserves all written data.
- CRC32C mismatch detected and logged on artificial corruption injection.
- Block-group tree readable independently of extent tree (mount-time scan skips extent tree).

### N2 — B-tree forest + checksums (6 weeks, 2 eng)

- Full 10-tree B-tree forest (root, extent, chunk, device, fs, csum, reflink, log,
  blockgroup, freespace).
- NvfsNodeHeader on every node with `generation` + `checksum` (Blake3 default).
- Merkle parent-stores-child checksum verification on every read (§3).
- Extent back-references: TREE_BLOCK_REF, SHARED_BLOCK_REF, EXTENT_DATA_REF,
  SHARED_DATA_REF (§5).
- Directory, inode, and file extent items in the FS tree.
- Basic `nvfs check` offline integrity tool.

**Acceptance:**
- Injected node corruption detected on read (not only on fsck).
- `nvfs check` reports backref inconsistencies after artificial corruption.
- Blake3 + CRC32C selectable per volume at mkfs time.

### N3 — Snapshots + reflink (5 weeks, 2 eng)

- Subvolumes (independent FS trees with ROOT_ITEM in root tree).
- Read-only and writable snapshots (tree-sharing + ref-increment).
- `nvfs snapshot create/delete/list`.
- Block cloning / reflink: `nvfs_reflink(src_fd, src_off, dst_fd, dst_off, len)` (§7).
- Backup roots in superblock (4-slot array) (§11).
- `nvfs rescue` (backup root selection + log replay).
- ARC cache (MRU+MFU+ghosts) (§13).

**Acceptance:**
- Snapshot creation is O(1) (< 1 ms on 1 TiB volume).
- `cp --reflink=always` on a 10 GiB file completes in < 100 ms (metadata-only).
- Snapshot deletion does not leak extents (verified by `nvfs check` after delete).
- ARC hit rate > 90% on hot metadata workload (LRU trace replay).

### N4 — Self-healing + scrub + send/receive (6 weeks, 2 eng)

- Per-chunk RAID profiles (Single, Dup, Mirror2, Mirror3, Mirror4) (§12).
- Self-healing on checksum mismatch (mirror consult + block rewrite) (§9).
- Online scrub background job with birth-gen pruning (§16.3).
- Send/receive: TLV stream, full and incremental (§10).
- Offline deduplication daemon (§8).
- `FsDriver` integration: `DriverInstance::Nvfs` in the shared FS driver interface.

**Acceptance:**
- Injected single-block corruption in Mirror2 chunk: repaired transparently, caller
  receives correct data.
- Incremental send of a 100 GiB snapshot after 1% change: stream size ≤ 2× change size.
- Scrub completes on a 1 TiB volume in < 4 hours at 50% I/O throttle.

### N5 — FDP optional path (3 weeks, 1 eng)

*(Unchanged from v1)*

- RUH allocation per class.
- PID-tagged writes.
- RU reclaim on discard.

**Acceptance:**
- FDP-capable drive shows measurable WAF reduction vs N4-conventional.
- Mount on non-FDP drive is unaffected (graceful fallback).

### N6 — Block cloning + offline deduplication (4 weeks, 1 eng)

- Expose `nvfs_reflink` as a proper syscall through the SimpleOS FS layer.
- `nvfs_reflink_extent_same` API for offline dedup daemon.
- Dedup daemon process: scan, hash, verify, reflink.
- `Capability::Dedup` advertisement.
- Integration test: 2× space savings on filesystem with 50% duplicate content.

**Acceptance:**
- Offline dedup reduces used space by ≥ 40% on synthetic duplicate dataset.
- No data corruption after dedup (verified by `nvfs check`).
- Dedup daemon exits cleanly if `Capability::Dedup` probe returns `None`.

### N7 — Native encryption + raw send (5 weeks, 2 eng)

- AES-256-GCM encryption with 3-level key hierarchy (§14).
- `nvfs send --raw` for encrypted raw send (§10.3).
- `nvfs change-key` (rewrap only, no re-encrypt).
- `Capability::Encrypt` advertisement.
- SHA256 checksum algorithm option (required for authenticated raw send).

**Acceptance:**
- Encrypted volume: random reads return correct plaintext after mount with correct key.
- Encrypted volume + wrong key: reads return `FsError::Corrupt` (auth tag failure).
- Raw send of encrypted snapshot: receiver stores ciphertext; integrity verified without
  decryption key.

### N8 — Block-group tree + online balance (3 weeks, 1 eng)

- Confirm block-group tree is correct (N1 shipped it; N8 validates it under load).
- Online balance: `nvfs balance convert=<profile> --class=<class>`.
- Device add/remove (requires balance to migrate data).
- `nvfs stats` reporting per-class space usage and RAID profile.

**Acceptance:**
- Mount time on 1 TiB volume: < 2 seconds (block-group tree avoids extent scan).
- Online balance of 100 GiB GENERAL_MUTABLE from Single to Mirror2: completes without
  data loss while simultaneous writes are active.

---

## 19. Capability table

| Capability | N1 | N2 | N3 | N4 | N5 | N6 | N7 | N8 |
|---|---|---|---|---|---|---|---|---|
| `COW` | Y | Y | Y | Y | Y | Y | Y | Y |
| `Checksum` | Y (CRC32C) | Y (Blake3) | Y | Y | Y | Y | Y | Y |
| `Snapshot` | - | - | Y | Y | Y | Y | Y | Y |
| `Clone` | - | - | Y | Y | Y | Y | Y | Y |
| `Reflink` | - | - | Y | Y | Y | Y | Y | Y |
| `SelfHeal` | - | - | - | Y | Y | Y | Y | Y |
| `SendReceive` | - | - | - | Y | Y | Y | Y | Y |
| `Dedup` | - | - | - | - | - | Y | Y | Y |
| `Encrypt` | - | - | - | - | - | - | Y | Y |
| `Scrub` | - | - | - | Y | Y | Y | Y | Y |
| `Compress` | - | - | - | - | - | - | - | future |
| `PosixCompat` | - | - | - | Y* | Y | Y | Y | Y |
| `Quota` | - | - | - | - | - | - | - | future |

*PosixCompat via `NvfsPosixDriver` (see §20); not the native driver.

---

## 20. Cross-references

- **`doc/05_design/fs_driver_interface.md`** — defines `FsDriver` trait, `DriverInstance`
  enum, `Extension` enum, `Capability` enum. NVFS-native implements
  `DriverInstance::Nvfs(NvfsDriver)`. NVFS-POSIX implements
  `DriverInstance::NvfsPosix(NvfsPosixDriver)`. N4 milestone plugs NVFS in as a live
  driver.
- **`doc/05_design/nvfs_posix_wrapper.md`** — full design of the POSIX-over-NVFS shim.
  The shim sits above the native NVFS driver and emulates `pwrite`/`ftruncate`/`rename`/
  `unlink`/`mmap` semantics via arena CoW. Callers must explicitly mount the
  `NvfsPosixDriver` variant to use the shim.
- **`doc/05_design/nvfs/svllm_requirements.md`** — svllm class taxonomy (`tensor_pack`,
  `manifest`, `adapter`, `append_only`, `temp`, `kv_spill`, `mutable`) maps onto the six
  NVFS classes defined in §3. svllm does not use POSIX semantics (R7 explicit
  non-requirement); it uses the native driver.
- **`doc/05_design/nvfs/from_spostgre.md`** — spostgre contributions S1–S7. The
  `arena_clone_range` (S4), `atomic_pointer_record_publish` (S6), and
  `arena_fua_append` (S7) are load-bearing for N3's reflink and N4's send/receive.
- **`doc/05_design/spostgre_design.md`** — spostgre uses NVFS via the S1–S7 API. The
  pmap entry expansion in §17.2 does not break spostgre's `page_generation` field
  (retained at offset 0x18).

---

## 21. Open questions

- **OQ-1:** Delayed ref queue ordering — what crash-consistency tests are required before
  N2 ships? (Btrfs's delayed-ref bugs took years to stabilize.)
- **OQ-2:** Pmap entry migration — offline tool or in-place upgrade flag?
- **OQ-3:** ARC RAM budget — 25% of process RSS or configurable mount option?
- **OQ-4:** Compress capability — lz4 default vs zstd opt-in; which milestone?
- **OQ-5:** RAID5/6 — when does the stripe-journal design land? Future phase post-N8.
- **OQ-6:** Quota tree — qgroup-style or simple per-subvolume limit?
- **OQ-7:** Encryption default — opt-in (like ZFS) or opt-out? Recommendation: opt-in.
- **OQ-8:** L2ARC (SSD read cache tier) — useful for NVFS if running on spinning disks;
  skip for pure-NVMe deployments.
