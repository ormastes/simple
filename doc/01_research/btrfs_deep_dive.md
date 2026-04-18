# Btrfs Deep Dive for NVFS Porting

**Status:** Phase 2 research deliverable for NVFS (2026-04-17).
**Companion docs:** `doc/05_design/nvfs_design.md`, `doc/05_design/nvfs/from_spostgre.md`, `doc/01_research/spostgre_research.md`.
**Intent:** Catalogue Btrfs mechanisms precisely enough that NVFS can KEEP, ADAPT, SKIP, or ATTACH each one under the NVFS capability model.

## 1. Executive summary

Btrfs is a copy-on-write (CoW), B-tree-forest filesystem whose on-disk state is a set of cooperating B-trees indexed by a 136-bit compound key `(objectid, type, offset)`. Writes never modify blocks in place; a new extent is allocated, its parent tree node is rewritten to point at the new extent, and the chain of rewrites ripples upward until a new root is written and the superblock is updated in a single transaction commit. Every metadata block carries a CRC32C (or, optionally, xxhash64 / sha256 / blake2b-256) over its full contents; every data extent carries a separate checksum item in a dedicated tree. RAID is expressed as a mapping from a logical address space into one or more device stripes via the chunk tree, so each block group can independently choose a RAID profile and be relocated by the balance code. Snapshots are cheap because a snapshot is just a new root item that shares the entire source subvolume's tree until CoW diverges.

The corpus of primary sources this report is grounded in:

1. **Ohad Rodeh**, "B-trees, Shadowing, and Clones," ACM Transactions on Storage 3(4), 2008 — the theoretical basis for Btrfs's CoW B-tree and for shared subtrees with ref-counted clones. Preprint: <https://www.usenix.org/legacy/event/lsf07/tech/rodeh.pdf>.
2. **Rodeh, Bacik, Mason**, "BTRFS: The Linux B-Tree Filesystem," ACM Transactions on Storage 9(3), article 9, 2013 — the canonical description of the shipping design. DOI: <https://doi.org/10.1145/2501620.2501623>.
3. **Linux kernel Documentation** — `Documentation/filesystems/btrfs.rst` and the `fs/btrfs/` source tree (kernel 6.11 at time of writing). The on-disk structures live in `fs/btrfs/ctree.h` and `include/uapi/linux/btrfs_tree.h`.
4. **btrfs-progs** user-space tools (`btrfs-progs.git`, <https://git.kernel.org/pub/scm/linux/kernel/git/kdave/btrfs-progs.git>), especially `check/`, `image/`, `send-dump.c`, and `Documentation/`.
5. **kernel.org Btrfs wiki** mirrors at <https://btrfs.readthedocs.io/en/latest/> (the documentation was migrated from the original kernel.org wiki and is now maintained in-tree).
6. **LWN article series** from 2007 forward — Corbet's introduction ("A short history of btrfs", <https://lwn.net/Articles/342892/>, 2009), the 2014 "Btrfs: Working with multiple devices" series, the 2017 "Status of Btrfs RAID5/6" (<https://lwn.net/Articles/720821/>), and the 2022 "Block group tree" landing (<https://lwn.net/Articles/899810/>).
7. **Chris Mason's** original announcement (btrfs mailing list, 12 June 2007, <https://lore.kernel.org/linux-btrfs/20070612101134.GA15126@think.oraclecorp.com/>) and his FOSDEM 2009 / Linux.conf.au 2012 talks.
8. **Btrfs send stream format** specification in `Documentation/btrfs-send-stream-format.rst` (in-tree since 2015).
9. **Bacik**'s Free Space Tree writeup and the associated patch series (<https://lwn.net/Articles/663021/>, 2015), "Block Group Tree" (v2 2022), and the scrub/replace infrastructure notes.

This is primary-source material. Where Btrfs documentation is ambiguous (most notably around RAID5/6 write-hole semantics, qgroup rescan consistency, and free-space-tree recovery edge cases), the report says so rather than inventing a single answer.

### 1.1 Why Btrfs matters to NVFS

NVFS's existing physical model is an append-only arena with a capability-probed NVMe path (ZNS, FDP, Copy, KV). Btrfs is the closest production-scale example of a CoW filesystem that ships features that NVFS is planning: snapshots, reflink clones, send/receive, per-block checksums, scrub-based self-healing, and user-visible RAID-like redundancy. Btrfs also has well-documented failure modes (RAID5/6 write hole; qgroup scale; ENOSPC behavior under small-device workloads). Studying both the successes and the cautionary tales is the point of this deep dive.

## 2. On-disk layout

### 2.1 Superblocks

Btrfs keeps up to **three** superblocks at fixed byte offsets from the start of each device: `0x10000` (64 KiB), `0x4000000` (64 MiB), and `0x4000000000` (256 GiB) — see `fs/btrfs/disk-io.c` (`BTRFS_SUPER_MIRROR_MAX = 3`) and `volumes.c` (`btrfs_sb_offset`). Copies that fall beyond the device's size are simply absent. Each superblock is 4096 bytes (`BTRFS_SUPER_INFO_SIZE`), regardless of device sector size, and contains:

- 32-byte **CSum** of the remainder of the superblock. For non-CRC32C profiles the prefix of a longer checksum is placed in this field.
- 16-byte **fsid** identifying the filesystem, followed by the current device's **dev_item.fsid** (normally equal; differs during device replace).
- `bytenr`, the logical address at which this superblock lives (used to detect accidental clobber).
- 64-byte **magic** `_BHRfS_M` (`0x4D5F53665248425F`).
- 64-bit **generation** — monotonically increasing commit counter. The highest-generation valid superblock on each device wins at mount.
- `root`, `chunk_root`, `log_root` — logical addresses of the root of the root tree, the chunk tree, and the log tree (the last is 0 when no log is pending).
- `total_bytes`, `bytes_used`, `num_devices`, `sectorsize`, `nodesize` (default 16 KiB since 3.14), `leafsize` (historical, now equal to nodesize), `stripesize`.
- `incompat_flags` bit field — mount-time gate on features the kernel must understand (`MIXED_BACKREF`, `DEFAULT_SUBVOL`, `MIXED_GROUPS`, `COMPRESS_LZO`, `COMPRESS_ZSTD`, `BIG_METADATA`, `EXTENDED_IREF`, `RAID56`, `SKINNY_METADATA`, `NO_HOLES`, `METADATA_UUID`, `RAID1C34`, `ZONED`, `EXTENT_TREE_V2`, `BLOCK_GROUP_TREE`, `RAID_STRIPE_TREE`).
- `compat_ro_flags` — the filesystem can mount read-only on kernels missing these (notably `FREE_SPACE_TREE` and `FREE_SPACE_TREE_VALID`).
- 35-byte `label`.
- `csum_type` — CRC32C (0), xxhash64 (1), sha256 (2), blake2b-256 (3). Documented in `fs/btrfs/fs.h` (`btrfs_csum_type`).
- Embedded `system_chunk_array` — a copy of enough CHUNK_ITEMs from the chunk tree to resolve the chunk tree root itself (bootstrap chicken-and-egg). This is the only data structure that the superblock carries by value rather than by reference.

**Rotation / commit strategy.** On every transaction commit, Btrfs writes all three superblocks with the new generation and a fresh checksum; the order is chosen so that if the system crashes during the write, at least one copy is left consistent (see `write_all_supers` in `disk-io.c`). Mount prefers the highest-generation superblock that passes its own checksum on each device; if a device's copies disagree, a scrub can repair the stale copies from the freshest.

Primary sources:
- `fs/btrfs/disk-io.c:write_all_supers` (kernel 6.11).
- `include/uapi/linux/btrfs.h:btrfs_super_block`.
- Rodeh/Bacik/Mason 2013 §3.1.

### 2.2 The tree forest

Btrfs is not "a filesystem with one tree." It is a **forest** of B-trees, each keyed the same way but owning a distinct slice of the information. All trees share the same node size (default 16 KiB, historically 4 KiB) and the same ItemKey encoding. The design motive is that each tree can evolve its format independently — a new tree can be added in a kernel release without a format break, an old tree can be retired by moving its items into a replacement, and one tree's internal fragmentation does not bleed into another's.

The trees:

1. **Root tree** (objectid `BTRFS_ROOT_TREE_OBJECTID = 1`). A directory of all other trees. Each entry is a `ROOT_ITEM` (or `ROOT_BACKREF`, `ROOT_REF`) keyed by the tree's objectid. Given only the superblock and this tree, you can locate every other root. The root tree is itself a CoW B-tree, and its own bytenr is written into the superblock.
2. **Chunk tree** (`BTRFS_CHUNK_TREE_OBJECTID = 3`). Maps chunks of logical address space onto stripes of physical devices. Each CHUNK_ITEM spans a `chunk_length` range of logical address starting at `chunk_offset` and holds `num_stripes` `btrfs_stripe` entries, each pointing at `(devid, physical_offset, dev_uuid)`. The chunk tree also contains DEV_ITEMs (one per device) keyed by devid.
3. **Device tree** (`BTRFS_DEV_TREE_OBJECTID = 4`). Inverse of the chunk tree's device half: keyed by `(devid, DEV_EXTENT, physical_offset)`, each DEV_EXTENT maps a physical extent on a device back to the logical `chunk_offset` that owns it. This is the structure walked by `btrfs device remove`, `balance`, and `replace`.
4. **Extent tree** (`BTRFS_EXTENT_TREE_OBJECTID = 2`). The allocator's book. Records every non-free logical extent as an EXTENT_ITEM (bytenr as objectid, `BTRFS_EXTENT_ITEM_KEY`, length as offset). Each extent carries one or more **back-references** (a.k.a. "backrefs") pointing to the fs-tree ref that owns it. Backrefs are what make offline fsck and scrub practical — given a corrupt data block you can walk up to the owning inode. With `SKINNY_METADATA` (on by default since mkfs.btrfs 3.18), metadata extents use a compact `METADATA_ITEM_KEY` form.
5. **FS tree** a.k.a. **subvolume tree**. One per subvolume; the top-level fs tree lives at `BTRFS_FS_TREE_OBJECTID = 5`. Each contains `INODE_ITEM`, `INODE_REF` / `INODE_EXTREF`, `DIR_ITEM`, `DIR_INDEX`, `XATTR_ITEM`, `EXTENT_DATA` — the actual file content. Snapshots and clones create additional fs trees with objectids `>= 256`.
6. **Checksum tree** (`BTRFS_CSUM_TREE_OBJECTID = 7`). A flat map from data extent logical bytenr to an array of per-sector checksums. Key is `(EXTENT_CSUM_OBJECTID = -10, CSUM, bytenr)`. Checksum size varies with `csum_type`. Metadata pages carry their own checksum inline in the node header (see §2.4), so they are not covered here.
7. **UUID tree** (`BTRFS_UUID_TREE_OBJECTID = 9`). Maps subvolume UUIDs to subvolume objectids. Enables `btrfs subvolume show <path>` and is rebuilt lazily.
8. **Free-space tree** (`BTRFS_FREE_SPACE_TREE_OBJECTID = 10`, compat_ro feature). Replaces the old per-block-group `FREE_SPACE_INODE` hidden file (the "space_cache_v1" mechanism). See §10.
9. **Log tree** (`BTRFS_TREE_LOG_OBJECTID = -6` in-memory, persisted under a ROOT_ITEM whose key is the fs-tree id it logs). A fast per-transaction journal for fsync; destroyed at every commit. See §8.
10. **Block group tree** (`BTRFS_BLOCK_GROUP_TREE_OBJECTID = 11`, incompat feature added in kernel 6.1, mkfs flag `-O block-group-tree`). Moves the BLOCK_GROUP_ITEMs out of the extent tree to cut mount time on large filesystems (LWN, Oct 2022).
11. **Quota tree** (`BTRFS_QUOTA_TREE_OBJECTID = 8`, conditional on `btrfs quota enable`). Holds QGROUP_INFO / QGROUP_LIMIT / QGROUP_RELATION items.
12. **Raid-stripe tree** (`BTRFS_RAID_STRIPE_TREE_OBJECTID = 12`, incompat `RAID_STRIPE_TREE`, mainlined for zoned-RAID work ~6.4). Stores per-stripe logical→physical mappings independently of the chunk tree so that zoned devices can reshuffle parity blocks without rewriting a whole chunk.

The forest is the key design decision. Because each tree is independently rooted in the root tree, adding a new kind of metadata does not require touching the format of existing trees — just allocate a tree objectid, bump `incompat_flags` (or `compat_ro_flags`), and ship. The Free-Space Tree and Block-Group Tree were added this way years apart.

Primary sources:
- Rodeh/Bacik/Mason 2013 §3.
- `include/uapi/linux/btrfs_tree.h` (all tree objectid constants; item type constants with values `1..252`).
- `fs/btrfs/disk-io.c:btrfs_read_roots` (mount-time tree loading).
- LWN "Btrfs block-group tree," 2022-10-05, <https://lwn.net/Articles/899810/>.

#### 2.2.1 Tree-by-tree detail

The **root tree** is the bootstrap. After reading the chunk tree (itself bootstrapped from the superblock's embedded system-chunk array; see §2.1), the kernel reads the root-tree root at `super.root`. Every other tree is located by a lookup in the root tree keyed by the tree's objectid. This is also where `ROOT_REF` and `ROOT_BACKREF` items live; they record parent/child subvolume relationships so that `btrfs subvolume show` can present a human-friendly path without walking the fs tree.

The **extent tree** is the most-written tree in a typical workload. Every allocation produces an `EXTENT_ITEM` (or `METADATA_ITEM` under `SKINNY_METADATA`) plus at least one backref. Every free removes them. Because the extent tree is itself CoW, a single extent allocation plus its backref costs potentially several tree-block CoWs on ancestors. The kernel amortizes this by batching into **delayed refs** (`fs/btrfs/delayed-ref.c`): modifications are staged in an in-memory red-black tree, then flushed at commit time into the extent tree as a compact sequence. The delayed-ref machinery is one of the least-documented and most historically-bug-prone parts of Btrfs; it is also the single biggest difference from naive CoW implementations.

The **chunk tree** is tiny (one CHUNK_ITEM per 1 GiB of filesystem is the default; for big filesystems this is still at most a few thousand items) and rarely-updated (only allocations that cross a chunk boundary or add/remove chunks modify it). It lives separately from the root tree so that chunk-tree corruption can be diagnosed and repaired without touching the root tree.

The **device tree** is the inverse half: one `DEV_EXTENT` per physical extent per device. `btrfs device delete` walks this tree to find out which logical chunks need to be relocated. `btrfs balance` with a `devid=` filter likewise walks this tree. On multi-device filesystems, this tree can have tens of thousands of items — comparable in size to a small fs tree.

The **fs tree** (subvolume tree) is where user-facing metadata lives. Its shape changes with workload: read-heavy fs trees are mostly INODE_ITEMs with few back-refs, write-heavy fs trees carry many EXTENT_DATA items pointing at many small extents, and fs trees of snapshot sources plus their snapshots share a large fraction of their tree blocks until writes diverge.

The **checksum tree** is a linear-in-data-size structure. Each entry covers one block-size region and stores a checksum per sector. For CRC32C the storage overhead is about 0.1 % of data (4 bytes per 4 KiB). For blake2b-256 / sha256 it is about 0.8 %.

The **UUID tree** is keyed by the 128-bit subvolume UUID split into two 64-bit halves for `objectid` and `offset`; the item payload is the subvolume's objectid in the root tree. This lets `btrfs subvolume list -u` answer in O(log n) without walking all subvolumes. It is lazily maintained — a stale UUID tree can be rebuilt on mount with `rescue=uuid_tree_rebuild`.

The **free-space tree** holds either EXTENT- or BITMAP-formatted free-space items per block group. The representation is chosen per-block-group at write time: dense block groups (many small free regions) use bitmaps, sparse ones use extent lists. The granularity is `sectorsize` (usually 4 KiB). Detail in §12.

The **log tree** is transient. It is created on first fsync in a transaction, grown by each subsequent fsync, and destroyed at commit. On crash, it is the "recent-fsync redo log." Its root is stored directly in the superblock (`super.log_root`), not in the root tree, so that a commit that failed between writing the root tree and writing the superblock still leaves a replayable log. See §8.

The **block-group tree** holds `BLOCK_GROUP_ITEM` entries — one per block group. Before kernel 6.1, these lived in the extent tree, where they formed a scattered minority interleaved with every extent allocation. Mounting required scanning every leaf of the extent tree looking for them. The Block Group Tree incompat feature isolates them into their own tree, dropping mount time on large filesystems from minutes to seconds (LWN, 2022).

The **quota tree** holds QGROUP_INFO, QGROUP_LIMIT, and QGROUP_RELATION items, present only if `btrfs quota enable` has ever been run. See §11.

The **raid-stripe tree** (incompat, new) stores per-stripe logical-to-physical mappings independently from the chunk tree. The motive is zoned-device RAID: because a zoned device can only append to a zone in strict order, the parity placement within a stripe must sometimes be reshuffled to respect that order, and the chunk tree's one-chunk-one-stripe-layout assumption does not hold.

### 2.3 Key / item format

Every item in every tree is addressed by a **136-bit compound key**:

```
struct btrfs_key {
    __u64 objectid;   /* what you're talking about */
    __u8  type;       /* what aspect of it */
    __u64 offset;     /* disambiguator, usually byte offset or hash */
};
```

Example keys that show how the compound design pays off in one tree:

| objectid | type | offset | meaning (in an fs tree) |
|---|---|---|---|
| inode_id | `INODE_ITEM (1)` | 0 | inode fields |
| inode_id | `INODE_REF (12)` | parent_inode_id | directory back-reference |
| inode_id | `XATTR_ITEM (24)` | name_hash | extended attribute |
| inode_id | `DIR_ITEM (84)` | name_hash | directory entry by name hash |
| inode_id | `DIR_INDEX (96)` | seq | stable enumeration order |
| inode_id | `EXTENT_DATA (108)` | file_offset | file content pointer |

In the extent tree:

| objectid | type | offset | meaning |
|---|---|---|---|
| bytenr | `EXTENT_ITEM (168)` | length | extent allocation |
| bytenr | `METADATA_ITEM (169)` | level | skinny metadata allocation |
| bytenr | `TREE_BLOCK_REF (176)` | tree_id | back-ref: used by a tree block |
| bytenr | `SHARED_BLOCK_REF (182)` | parent_bytenr | back-ref: shared tree block |
| bytenr | `EXTENT_DATA_REF (178)` | hash | back-ref: file data reference |
| bytenr | `SHARED_DATA_REF (184)` | parent_bytenr | back-ref: shared data reference |

Ordering is lexicographic on `(objectid, type, offset)` interpreted as unsigned big-endian. This is why `DIR_ITEM` and `DIR_INDEX` live next to each other under the same inode — a directory readdir is a single range scan, and all xattrs for an inode are also contiguous.

All item types are enumerated in `include/uapi/linux/btrfs_tree.h`. The official constants are the authoritative reference; anything the mailing list calls "well-known item types" without pointing at that file is suspect.

**A worked example of why the compound key matters.** Suppose we want to list all extended attributes of inode 17. The naive design would need a secondary index from inode to xattrs. Btrfs instead seeks the tree to `(objectid=17, type=XATTR_ITEM, offset=0)` and iterates forward until the key leaves the `type=XATTR_ITEM` range. Every xattr of inode 17 is guaranteed contiguous in key-order, and therefore contiguous in leaf-order, and therefore read in a single leaf in the common case — no secondary index. The same pattern applies to directory enumeration (DIR_INDEX), file extent enumeration (EXTENT_DATA), and every other per-inode list. The `type` byte is a miniature namespace inside the key, and ordering is designed so that the lists that are read together are stored together.

**Overflows.** A few item types need more space than a leaf can hold. INODE_REF items are variable-length because a filename is variable-length; if many files have the same hash in a directory, the DIR_ITEM payload is a linked list of dir-item entries, not a single fixed record. The INODE_EXTREF item is the second-generation fallback for when an inode has more hard links than fit in a single INODE_REF chain.

**Skinny metadata.** The `SKINNY_METADATA` incompat feature renames `EXTENT_ITEM_KEY` to `METADATA_ITEM_KEY` for tree-block extents only, using the offset field to carry the level of the tree block rather than its length (which is always `nodesize`). This saves about 8 bytes per metadata extent and was made default in mkfs.btrfs 3.18 (2014). Consumers that read the extent tree must handle both key variants.

### 2.4 Node and leaf layout

A B-tree block is exactly `nodesize` bytes (default 16 KiB). It starts with a **`btrfs_header`**:

```
__u8  csum[BTRFS_CSUM_SIZE];   /* 32 bytes */
__u8  fsid[16];
__le64 bytenr;                 /* own logical address */
__le64 flags;
__u8  chunk_tree_uuid[16];
__le64 generation;
__le64 owner;                  /* tree objectid */
__le32 nritems;
__u8   level;
```

Total header size is 101 bytes (padded to 8); this is why the kernel maintains `BTRFS_LEAF_DATA_SIZE = nodesize - sizeof(btrfs_header)` and measures leaf free space against that.

A **leaf** (level 0) stores `nritems` fixed-size `btrfs_item` slots starting right after the header and grows downward, while variable-length item data grows upward from the end of the block:

```
[header | item0 | item1 | ... | itemN-1 | ... FREE ... | dataN-1 | ... | data1 | data0 ]
```

Each `btrfs_item` is `(key, offset_into_block, size)` so items can be relocated without touching the data payload. Leaves split when their item array and data body meet in the middle; merges happen during deletions to keep each leaf at least about 25 % full.

A **node** (level > 0) stores `nritems` `btrfs_key_ptr` entries, each `(key, block_ptr, generation)`. `generation` is the transaction id that last touched the child — a lightweight way to detect stale mirror copies without chasing down to the leaf.

**CRC32C integrity.** The header's `csum` field covers the entire block from byte 32 to byte `nodesize-1`. With `csum_type = CRC32C` only the first 4 bytes of `csum` are used; with sha256 / blake2b-256 the full 32 bytes are used. The checksum is recomputed on every CoW rewrite of the block, so there is no "stale checksum" failure mode for metadata. Data checksums live in the checksum tree.

Because nodes include their own `bytenr` in the header, reading a block into memory and finding the bytenr doesn't match means either a torn write or a misdirected read — Btrfs aborts the read and falls back to a mirror copy if one exists. This is the key to Btrfs's self-healing story: the error detection is in the data plane, not in a separate scrubber.

Primary sources:
- `include/uapi/linux/btrfs_tree.h:btrfs_header`, `btrfs_item`, `btrfs_key_ptr`.
- `fs/btrfs/ctree.c:btrfs_search_slot`, `leaf_space_used`, `btrfs_leaf_free_space`.

**Node size choice.** Before 3.14, Btrfs defaulted to a 4 KiB node size (matching page size on x86_64). The 3.14 `BIG_METADATA` incompat change moved the default to 16 KiB. Larger nodes reduce tree height (log base `fanout`), cut the number of blocks touched on CoW ripples, and improve branching factor, at the cost of read amplification when only one item from a large leaf is needed. The kernel supports any power of two from 4 KiB to 64 KiB; the practical tested range is 4–64 KiB. For ARM64 with 64 KiB pages, 64 KiB is the natural node size. For Simple-OS targets with 4 KiB pages, 16 KiB is a good default. NVFS inherits this choice and should pin a single size per-filesystem in its superblock.

**Integrity at the page level.** The `csum_type` pins the hash; the header's first 32 bytes are the hash output, and the remainder of the 16 KiB (or whatever nodesize is) is hashed into it. Metadata blocks that fail their checksum are re-read from a mirror (DUP, RAID1/1C3/1C4/RAID10) and, if a good copy is found, written back in-place over the bad mirror. The kernel logs `BTRFS warning (device X): transid verify failed` or `checksum verify failed` to dmesg, which is the first symptom of disk decay that administrators see.

### 2.5 Chunks, stripes, and RAID profiles

The **logical** address space Btrfs presents to itself runs from 0 to `super.total_bytes`. Nothing about logical bytenr encodes which device the data lives on — that is the **chunk tree**'s job. A `btrfs_chunk` item describes one contiguous logical range:

```
__le64 length;
__le64 owner;
__le64 stripe_len;       /* per-stripe size, default 64 KiB */
__le64 type;             /* DATA | METADATA | SYSTEM | profile bits */
__le32 io_align;
__le32 io_width;
__le32 sector_size;
__le16 num_stripes;
__le16 sub_stripes;
/* followed by num_stripes btrfs_stripe {devid, offset, dev_uuid} */
```

`type` packs the storage class and RAID profile in one word:

- Class bits: `BTRFS_BLOCK_GROUP_DATA (0x1)`, `METADATA (0x4)`, `SYSTEM (0x2)`. A chunk may carry both DATA and METADATA if `mixed-bg` is on (recommended for small filesystems only, `mkfs.btrfs -M`).
- Profile bits: `RAID0 (0x8)`, `RAID1 (0x10)`, `DUP (0x20)`, `RAID10 (0x40)`, `RAID5 (0x80)`, `RAID6 (0x100)`, `RAID1C3 (0x200)`, `RAID1C4 (0x400)`. With no profile bit set the profile is **single**.

Since the chunk tree owns the logical↔physical mapping, RAID is **per-chunk**, not per-filesystem. A filesystem can have DATA in RAID1 and METADATA in RAID1C3; a `balance` can rewrite chunks of one profile into chunks of another without touching the logical address space. This is why `btrfs balance convert=data,raid1:raid10` works and why the same mechanism supports online device removal.

Profiles (summary, per Btrfs docs `Documentation/filesystems/btrfs.rst` and <https://btrfs.readthedocs.io/en/latest/Volume-management.html>):

| Profile | min devs | copies | parity | useable % |
|---|---|---|---|---|
| single | 1 | 1 | 0 | 100 |
| DUP | 1 | 2 (same dev) | 0 | 50 |
| RAID0 | 2 | 1 | 0 | 100 |
| RAID1 | 2 | 2 | 0 | 50 |
| RAID1C3 | 3 | 3 | 0 | 33 |
| RAID1C4 | 4 | 4 | 0 | 25 |
| RAID10 | 4 | 2 | 0 | 50 |
| RAID5 | 2+ | 1 data + 1 parity / stripe | 1 | (n-1)/n |
| RAID6 | 3+ | 1 data + 2 parity / stripe | 2 | (n-2)/n |

**DUP** is Btrfs-specific: two copies on the **same** physical device, originally for protecting metadata on single-disk SSDs and laptops. The kernel will warn against DUP on "solid-state devices that dedupe" because the FTL may quietly coalesce the copies, defeating the purpose (`mkfs.btrfs(8)`).

**RAID1 in Btrfs is not classic mirror RAID.** Btrfs RAID1 means "two copies, each on a different device" — not "every device is a mirror of every other." In a three-disk RAID1 Btrfs, each chunk has two stripes on a pair of devices chosen so usage is balanced, and different chunks may live on different pairs. The chunk tree records the pair explicitly. This makes RAID1 scale to arbitrarily many devices but breaks the intuition that "N-disk RAID1 gives N copies" — you want RAID1C3 / RAID1C4 for that.

**RAID5/6** share the chunk mapping but additionally carry parity stripes. The well-known **write hole** is: a partial-stripe write updates some of the data stripes and the parity stripe, but if power fails between them, the parity no longer matches the data, and a later device failure means a replay can reconstruct wrong bytes. Btrfs's documented defense has been the 2020 partial-stripe read-modify-write mitigation plus scrub, not a dedicated journal; LWN <https://lwn.net/Articles/720821/> (2017) and the btrfs.readthedocs.io page "Status of RAID5/6" (current) both explicitly flag the write hole as the reason RAID5/6 stays marked *unstable for metadata* and cautioned for data. The in-development `RAID_STRIPE_TREE` (2023+) is the substrate expected to close this, first on zoned devices where the natural append ordering obviates the hole.

**Chunk allocation sizing.** A `single` DATA chunk defaults to 1 GiB, a METADATA chunk to 256 MiB, and a SYSTEM chunk to 32 MiB, with growth at allocation time toward larger chunks on larger filesystems. The kernel adjusts these heuristically based on `total_bytes` (see `btrfs_alloc_chunk`); small filesystems get small chunks to avoid wasting a single 1 GiB block group on a 2 GiB disk. RAID0 / RAID10 / RAID5 / RAID6 chunks spread their length across stripes, so the logical length of the chunk is `data-stripes * stripe_len` and may be larger than the single-chunk default.

**Per-class profile mixing.** `mkfs.btrfs -d raid1 -m raid1c3` is the common production setting: data in mirror-of-2 and metadata in mirror-of-3. Metadata is the load-bearing part of a Btrfs volume — losing a metadata block loses more than losing a data block — so metadata is usually kept at higher redundancy than data. NVFS should inherit this discipline in its per-arena profile policy.

**Read-side load-balancing.** Btrfs spreads reads across mirror copies by PID: `mirror_num = (pid % num_stripes) + 1`. This is a deliberately simple policy that gives parallel readers different mirrors without extra bookkeeping. The downside is that single-reader workloads always pick the same mirror, which can mask a failing device until scrub runs. The policy is documented in `fs/btrfs/volumes.c:find_live_mirror`.

### 2.6 Extent references

Every file-data extent is described by an `EXTENT_DATA` item in the fs tree:

```
__le64 generation;
__le64 ram_bytes;               /* logical (uncompressed) size */
__u8   compression;             /* 0=none 1=zlib 2=lzo 3=zstd */
__u8   encryption;              /* reserved */
__le16 other_encoding;
__u8   type;                    /* 0=inline 1=regular 2=prealloc */
/* if type == inline: raw bytes follow */
/* else: */
__le64 disk_bytenr;             /* logical byte in the extent tree */
__le64 disk_num_bytes;          /* size of the on-disk (possibly compressed) extent */
__le64 offset;                  /* start inside that extent */
__le64 num_bytes;               /* length of this reference */
```

The split between `disk_*` fields and `offset`/`num_bytes` is critical: one physical extent can be referenced by **many** `EXTENT_DATA` items at different offsets, which is the mechanism for reflinks (see §5). Inline extents live entirely in the leaf; they waste less space on small files but inflate metadata. `type == prealloc` is an allocated extent that reads as zeroes until first write — used by `fallocate(2)`.

The corresponding `EXTENT_ITEM` in the extent tree carries a refcount of references into it, plus a chain of back-reference items. Reflink decrements nothing; it only adds another `EXTENT_DATA_REF`. Deleting a file drops the ref and, when it reaches zero, the extent is released.

**Inline vs. shared.** The Btrfs docs explicitly say (see `Documentation/filesystems/btrfs.rst`) that inline extents are capped at `max_inline` (mount option, default `min(2048, nodesize/2)`) and that compression is applied before inlining. Shared (reflinked) extents survive every snapshot, CoW defrag, and send/receive; the in-tree `btrfs fi dup-extents` test coverage and the `btrfs_clone_file_range` ioctl source are the authoritative references.

Primary sources:
- `include/uapi/linux/btrfs_tree.h:btrfs_file_extent_item`.
- `fs/btrfs/file-item.c:btrfs_lookup_file_extent`.
- Documentation on extent backrefs in `Documentation/filesystems/btrfs.rst` §"Extent backrefs".

**Backref encoding (detail).** A data extent's backrefs live inside the `EXTENT_ITEM_KEY` entry in the extent tree. The kernel distinguishes **full** backrefs from **implicit** (ref-counted) backrefs using the `MIXED_BACKREF` incompat feature (default on since 2009). For modern filesystems, four backref item kinds cover the cases:

- `TREE_BLOCK_REF (176)` — "this metadata block is referenced by tree X's root." Carries `(root_id)`. Used for fs-tree tree blocks that are not shared across subvolumes.
- `SHARED_BLOCK_REF (182)` — "this metadata block is referenced by parent bytenr Y." Carries `(parent_bytenr)`. Emitted when a block is shared by multiple subvolumes (the same root pointer appears in more than one tree).
- `EXTENT_DATA_REF (178)` — "this data extent is referenced by inode `(root_id, inode_id)` at file offset `off`, `cnt` times." Compact; refcount-style.
- `SHARED_DATA_REF (184)` — "this data extent is referenced `cnt` times via parent bytenr Y." Used when a data extent is cloned across subvolumes that do not share the pointing tree block.

The distinction matters for snapshot delete: dropping a snapshot walks its tree and, for each block, decrements the appropriate backref. SHARED refs are stable across arbitrary subvolume reorganizations because they name a parent bytenr (which itself is refcounted); TREE_BLOCK_REFs require walking to find the original owner when the owning subvolume is deleted. The `MIXED_BACKREF` feature makes these two schemes interoperate in the same tree.

**Prealloc extents.** `fallocate(2)` allocates an `EXTENT_DATA` entry with `type = 2` (prealloc). Reads return zeros without consulting the extent tree for data; writes into the prealloc range convert it to a regular extent by splitting the prealloc entry and allocating (or using a cluster span of) real data. The transition is a single extent-tree update; the file content simply appears. For databases using `fallocate` to pin extents, this is the piece that preserves locality without paying for zeroing the disk up front.

## 3. Copy-on-write model

### 3.1 Shadowing

Btrfs implements Rodeh's **shadowing** discipline. Each tree node points to children by logical bytenr. A write that touches a node X produces a new block X' allocated from the free-space allocator; X's parent P is likewise CoW'd into P'; and so on up to the tree root. The old X remains valid for any reader holding the old root — e.g. a concurrent snapshot reader, or the replay log.

This single rule gives Btrfs:

1. **Crash atomicity.** Because the new root is only "in force" after the superblock's `bytenr` field (for the root tree) is updated, any crash before the superblock write leaves the filesystem pointing at the previous consistent state.
2. **Cheap snapshots.** A snapshot is just a new `ROOT_ITEM` in the root tree whose `bytenr` is the current snapshot-source's root. No data is copied.
3. **Read-only point-in-time views.** Any held root bytenr is a complete consistent view until the corresponding tree blocks are freed (and they won't be freed while their refcount is > 0).

The cost is write amplification: a single-byte change that CoWs a leaf also CoWs every ancestor node. Btrfs limits this by (a) batching many logical changes into one transaction (so ancestor CoW amortizes), (b) inlining small data into leaves, (c) the `SKINNY_METADATA` format.

### 3.2 Transaction groups and generation numbers

The filesystem's global monotonic counter is the **generation** (a.k.a. `transid`). Every tree block header carries the generation at which it was written; the superblock carries the generation it committed at. A block whose generation is higher than the currently-active root's is a block that will not be reachable from the next mount's state — unless the superblock catches up.

`btrfs_commit_transaction` (`fs/btrfs/transaction.c`) is the commit pipeline. It:

1. Waits for all writers to drop their join references.
2. Flushes all dirty inode data via `btrfs_start_delalloc_roots` so data extents reach disk before the metadata that references them (ordered data, the default).
3. Writes out the extent allocator's dirty trees (delayed refs, chunks, devices).
4. Walks the dirty-root list and writes each root out; for each, the leaves first, then the nodes, then the new tree root's bytenr into the root tree.
5. Writes the root tree.
6. Flushes the device caches.
7. Writes the three superblocks with the new `generation` and root pointers.
8. Flushes the device caches again.

Steps 6 and 8 are `BLKDEV_ZERO_FLUSH` / `REQ_PREFLUSH | REQ_FUA`; they are the barrier that makes CoW durable. The Btrfs docs explicitly state (`mount` page, `flushoncommit` section) that the default is to flush on commit and that turning it off is acceptable only for disposable filesystems.

### 3.3 Space reservation

The allocator must never over-promise — if a metadata operation starts and midway through finds there is no free space for a CoW, the filesystem is stuck. The kernel tracks:

- `global_block_rsv`, a permanent reserve big enough to complete an in-flight commit.
- `trans_block_rsv`, the current transaction's reservation bucket.
- `delayed_refs_rsv` and `delayed_rsv` for deferred backref updates.
- Per-operation calls to `btrfs_reserve_metadata_bytes(mkdir_items)` etc., which refuse an operation with `-ENOSPC` before any state is mutated.

Historical Btrfs struggled here. Modern (6.x) kernels are much more forgiving, but NVFS designers should note the rule: "reserve before you mutate" is not optional in a CoW filesystem.

Primary sources:
- Rodeh 2008 §3, §4 on shadowed B-trees.
- `fs/btrfs/transaction.c:btrfs_commit_transaction`.
- `fs/btrfs/block-rsv.c`.
- LWN "Btrfs and ENOSPC" (various, 2010–2014).

### 3.4 Delayed refs in detail

The CoW discipline would naively require that every inode write allocate a new extent and update the extent tree backrefs synchronously. On a write-heavy workload this would cripple throughput because every logical write multiplies into several tree-block CoWs — ancestor nodes in the fs tree, ancestor nodes in the extent tree, and the chunk tree if a new chunk must be allocated. Btrfs breaks this cycle with **delayed refs**: the fs-tree side of the write commits immediately (the inode's EXTENT_DATA is written), but the extent-tree backref update is queued into an in-memory red-black tree and flushed into the extent tree in bulk at commit time.

`fs/btrfs/delayed-ref.c` implements the queue. Each entry is an "add `n` refs to extent X with backref Y" or "drop `n` refs from extent X". At commit, the queue is sorted by `(bytenr, then operation)` and flushed; many operations against the same extent collapse into a single net-change. This is why Btrfs's commit time is super-linear in the number of recent writes — the queue can grow large — but the per-write amortized cost is small.

The delayed-ref machinery has historically been one of Btrfs's largest bug surfaces. Misordered queue draining, race conditions between background flushers and commit, and accounting drift between the on-disk extent refcount and the in-memory delayed count are classic Btrfs bugs. Any NVFS design that adopts delayed refs (we should) must plan for exhaustive test coverage of the queue's semantics. The current test harness in `fs/btrfs/tests/` and the out-of-tree `btrfs/fstests` (xfstests) suite are the references.

### 3.5 Transaction nesting and commit throttling

A Btrfs transaction is a named handle; `btrfs_start_transaction(root, num_items)` reserves metadata slots and returns a handle. Operations that need more reserve can call `btrfs_extend_transaction(handle, extra_items)`. Multiple operations running concurrently share the transaction by joining (incrementing a reference counter on the current `btrfs_transaction`).

Commit cadence is controlled by:

- `commit=<N>` mount option (default 30 seconds). The background thread `btrfs-transaction` wakes every N seconds and forces a commit if any writer has finished.
- Threshold on delayed-ref queue size. Large queues trigger early commit.
- Explicit `sync(2)` / `syncfs(2)` calls.
- `fsync(2)` on an inode does **not** trigger a full commit; it writes into the log tree (see §8).

The "ordered data" mode means that a transaction's commit pipeline flushes all data extents before the metadata referencing them. This is the default; there is no `data=writeback` equivalent to ext4's fast-and-loose mode. The absence of writeback mode is a deliberate safety choice and should be matched in NVFS.

## 4. Subvolumes and snapshots

### 4.1 Subvolume = fs tree

A subvolume is a root entry in the root tree referencing an fs tree; to the VFS it is a directory with its own inode-number space. Because fs trees share the same extent tree, a file reflinked across two subvolumes is one extent with two `EXTENT_DATA_REF` items.

Every Btrfs filesystem has `BTRFS_FS_TREE_OBJECTID = 5` as its top-level subvolume; additional subvolumes get objectids ≥ 256 assigned from `super.generation`. The top-level can be mounted via `subvolid=5` at any time regardless of what subvolume is the default, which is the supported recovery path.

### 4.2 Snapshot = clone of an fs tree

`btrfs subvolume snapshot` creates a **writable** clone of a subvolume: it allocates a new root objectid, writes a new `ROOT_ITEM` pointing at the same root bytenr as the source, and bumps a refcount on that block. A readonly snapshot is identical except the fs tree is flagged read-only (`ROOT_SUBVOL_RDONLY`).

Creation is O(1). Divergence is O(changes). Deletion is O(blocks unshared), because each tree block carries a refcount and freeing a snapshot walks its blocks dropping refs; blocks still shared with another subvolume stay live. This is what Rodeh 2008 calls "refcounted clones": the refs live in the extent tree as `TREE_BLOCK_REF` and `SHARED_BLOCK_REF` backrefs.

The refcount scheme has a subtle property: the "first-writer-after-split" pays the CoW, but the "second-writer-of-a-shared-block" sees the block as already split and pays no CoW. This matters for NVFS: the amortized cost of a modify-after-snapshot is not 1 CoW per modification but 1 CoW per *block first touched after the snapshot*.

### 4.3 Deletion

`btrfs subvolume delete` marks the subvolume dead and schedules `btrfs-cleaner` to walk the fs tree dropping refs. The user-facing call returns once the ROOT_ITEM is removed; the actual block freeing proceeds in the background. Primary source: `fs/btrfs/transaction.c:clean_dirty_subvols` and `root-tree.c:btrfs_del_root`.

Read-only snapshots can be mounted individually (`mount -o subvol=snapshot_name`). The `send` workflow depends on rw-to-ro snapshots to get a stable generation boundary.

Primary sources:
- Rodeh/Bacik/Mason 2013 §4.2 on shadowing with refcounts.
- `Documentation/filesystems/btrfs.rst` "Subvolumes" section.
- Btrfs wiki "SysadminGuide" <https://btrfs.readthedocs.io/en/latest/SysadminGuide.html>.

### 4.4 Nested subvolumes

Subvolumes can contain other subvolumes, but the containment is purely a path-based illusion: a nested subvolume's fs tree is independent of its parent's fs tree, and a snapshot of the parent does **not** automatically snapshot the child. This is a common surprise for users; `btrfs subvolume snapshot -r` does not recurse by design. The workaround is to snapshot each subvolume individually, typically driven by a userspace tool like `btrbk` or `snapper`.

The implication for NVFS is the opposite: because NVFS organizes by storage class and not by directory tree, a "snapshot" there is already by-class and the nesting concept does not apply. This is one of the places where a fresh design gets to skip a decade of Btrfs confusion.

### 4.5 Default subvolume

The `DEFAULT_SUBVOL` incompat feature designates a non-FS_TREE subvolume as the root that gets mounted when no `subvol=`/`subvolid=` option is given. It is set with `btrfs subvolume set-default <id> <path>`. The top-level subvolume (objectid 5) is always mountable with `subvolid=5`, which is the recovery escape hatch if the default points at a missing or corrupt subvolume.

### 4.6 Snapshot lifecycle in practice

A typical Btrfs-based backup workflow (as documented by `btrbk`, snapper, and the Btrfs wiki):

1. Take a read-only snapshot of the source subvolume: `btrfs subvolume snapshot -r /data /snapshots/data.YYYY-MM-DDTHH:MM`.
2. `btrfs send` the snapshot to a backup destination; the first send is full, subsequent sends are incremental relative to the previously-sent read-only snapshot.
3. Retain a rolling window of local read-only snapshots (e.g. hourly for 24 h, daily for 30 d, monthly for 1 year); older snapshots are deleted.
4. The backup destination retains its own snapshots, similarly managed.

The cost of keeping 100 snapshots of a 1 TiB filesystem that changes 1 GiB per day is approximately: 1 TiB of shared data + 100 GiB of diverged extents + metadata proportional to the number of touched extents, typically 1–5 % of diverged-data size. This is the "Btrfs value proposition" that NVFS aims to match.

## 5. Reflinks and deduplication

### 5.1 Reflink = explicit shared-extent clone

`cp --reflink=always` and the `FICLONE` / `FICLONERANGE` ioctls call `btrfs_clone_file_range` (`fs/btrfs/reflink.c`), which walks the source file's `EXTENT_DATA` items in the given range and installs matching items in the destination file pointing at the same `(disk_bytenr, disk_num_bytes)` — bumping the extent's refcount. Data is not copied. Subsequent writes to either file CoW only the affected subrange.

Because the reflink is just another `EXTENT_DATA_REF` backref, the extent tree already knows the extent is shared and the allocator will not reuse it until all refs drop. NVFS's arena capability already supports the underlying operation (extent with multiple references); the piece to port is the **file-range ioctl surface**.

### 5.2 Out-of-band dedup

Btrfs ships `FIDEDUPERANGE` / `BTRFS_IOC_FILE_EXTENT_SAME` (`fs/btrfs/ioctl.c:btrfs_ioctl_file_extent_same`). The kernel is handed a "this extent in file A should be the same as that extent in file B" assertion; it **re-reads and compares** the two regions (under lock, to defeat TOCTOU) and only if the bytes match does it install a shared reference. The *discovery* of identical extents is entirely user-space — tools like `duperemove` (<https://github.com/markfasheh/duperemove>) and `bees` (<https://github.com/Zygo/bees>) hash-and-compare, then call the ioctl.

There is **no in-band Btrfs deduplication** shipping in mainline. Chris Mason's "Inline dedup" RFC series (2013) never merged. `btrfs-progs` has no deduplication subcommand — this is the wiki's explicit advice, repeated by LWN coverage of the duperemove/bees approach.

### 5.3 Cross-subvolume and cross-snapshot

Both `reflink` and `EXTENT_SAME` work across subvolumes on the same filesystem (the extent tree is global) but not across filesystems. Read-only snapshots refuse EXTENT_SAME on the read-only side.

Primary sources:
- `fs/btrfs/reflink.c` (merged 2020 as a refactor of `ioctl.c:btrfs_ioctl_clone_range_v2`).
- `Documentation/filesystems/btrfs.rst` "Reflink".
- duperemove README, bees README.

### 5.4 Reflink performance envelope

Reflink cost is roughly: `O(source_extents_in_range)` tree-walks on the source, plus `O(dest_extents_inserted)` writes on the destination, plus per-extent backref additions. For a 100 GiB VM image image-cloned into a 100 GiB destination, the typical time on a modern SSD is seconds, not minutes, because the extent count is typically in the thousands (Btrfs's extent-coalescing keeps it low). The subsequent first write to either side pays the CoW for a single extent only.

An important trap: reflinks interact with defrag. `btrfs filesystem defragment` rewrites fragmented extents into larger contiguous ones by **copying**, not by moving. This breaks sharing. A filesystem heavy on reflinks (container storage, VM farms) should run defrag **before** reflinking, never after. The wiki's defrag page (<https://btrfs.readthedocs.io/en/latest/Defragmentation.html>) calls this out in bold.

### 5.5 Duperemove and bees

`duperemove` is a batch-oriented dedup tool: it scans a directory tree, hashes extents (with a configurable hash algorithm), finds matches, and calls `FIDEDUPERANGE` on them. It runs off-line and is idempotent across invocations. `bees` (<https://github.com/Zygo/bees>) runs as a daemon, continuously scanning the filesystem's virtual extent tree with a bounded memory budget, and deduping incrementally. Bees is the closest Btrfs has to "online dedup" but it is still strictly out-of-band — the kernel is only involved as the target of `FIDEDUPERANGE` calls.

The lesson for NVFS is that the hash-and-compare loop belongs in userspace, and the kernel's role is to provide the atomic compare-and-share ioctl. Keeping this boundary simplifies both sides.

## 6. Checksums and self-healing

### 6.1 Checksum algorithms

The `csum_type` field in the superblock pins the algorithm for the lifetime of the filesystem (modulo a rewrite). Options (kernel 6.11):

- `BTRFS_CSUM_TYPE_CRC32C = 0` — 4 bytes; the historical default.
- `BTRFS_CSUM_TYPE_XXHASH = 1` — 8 bytes of xxhash64; fastest non-cryptographic.
- `BTRFS_CSUM_TYPE_SHA256 = 2` — 32 bytes; cryptographic, heaviest.
- `BTRFS_CSUM_TYPE_BLAKE2 = 3` — 32 bytes of blake2b-256; cryptographic, meaningfully faster than sha256 on CPUs without SHA-NI.

All algorithms write their full digest into the 32-byte `csum` header field for metadata and into the checksum tree for data. Shorter digests live in the first N bytes of the 32-byte slot; the rest is zero-filled. Primary source: `fs/btrfs/fs.h` `btrfs_csums[]`.

### 6.2 Read path and repair

On every metadata or data read the kernel:

1. Fetches the block from the primary mirror.
2. Recomputes the checksum.
3. If it matches, returns the data.
4. If it does not match, logs a corruption event, increments the per-device error counter, and retries from the next mirror (for DUP/RAID1/RAID1C3/RAID1C4/RAID10) or reconstructs via parity (for RAID5/RAID6).
5. If a good copy is found, it writes the good copy over the bad one in-flight. This is called **transparent repair** and is implemented in `fs/btrfs/volumes.c:btrfs_repair_one_sector` and `fs/btrfs/extent_io.c:btrfs_repair_eb_io_failure`.

For `nodatasum` inodes (see §6.4) the data read is returned without check; for `nodatacow` inodes the read is checked only if a checksum item happens to exist, which it won't for ongoing writes, so checking is effectively off.

### 6.3 Scrub

`btrfs scrub start` (`fs/btrfs/scrub.c`) reads every allocated extent of every block group on every device, recomputes the checksum, and repairs mismatches by pulling from a mirror. Design points:

- Scrub operates on **physical** stripes, walking dev_extents in order, to maximize sequential read throughput.
- It scales per-device (not per-cpu), using one worker per device.
- It reports `(read_errors, csum_errors, verify_errors, no_csum, csum_discards)` in `btrfs scrub status`.
- Scrub does not touch uncheckmsummed data (nodatasum) or unallocated space.
- For RAID5/RAID6 chunks, scrub reconstructs data when the data checksum fails *and* parity checks out; the documented caveat is that scrub alone cannot fix the write hole (§2.5), because a crashed partial-stripe write leaves both data and parity wrong together.

A notable failure mode: scrub on a RAID1 where both mirrors are corrupted in the same place cannot repair — it reports a double-corruption event. NVFS should plan for a similar reporting surface.

### 6.4 `nodatasum` and `nodatacow`

Two mount options / inode flags change the checksum and CoW behaviour:

- `nodatacow` (inode flag `NODATACOW`, applied to an empty file by `chattr +C`) — writes happen in place, without CoW. This is useful for large sequentially-rewritten files (VM images, big databases) to escape CoW overhead, but **it automatically implies `nodatasum`** for that inode, because Btrfs has no defined way to atomically update a checksum and a data block simultaneously when the data block is being overwritten. The docs warn that `nodatacow` plus a checksum mismatch on the remaining checksummed regions of the same inode will now silently fail.
- `nodatasum` (mount option, global) — disables checksumming of data blocks but not metadata. Metadata is always checksummed.

Snapshots of a `nodatacow` inode do CoW the **first** post-snapshot write, because two subvolumes cannot share a physical block if one of them plans to overwrite it in place.

Primary sources:
- `Documentation/filesystems/btrfs.rst` "Data and metadata checksums".
- `fs/btrfs/scrub.c`.
- `fs/btrfs/inode.c:btrfs_set_prop` (nodatacow implications).

### 6.5 Checksum cost and memory residency

Each checksum is looked up in the checksum tree during the read path. The kernel caches recently-read checksum-tree leaves in the page cache; hot ranges therefore have nearly zero checksum-lookup overhead. Cold ranges pay one random read per 256 KiB-or-so of data (one leaf covers roughly 120 EXTENT_CSUM entries, each of which covers one block-size region). Under random 4 KiB reads, this ~1 % overhead is noticeable; under any sequential pattern it rounds to zero.

The alternative — inline per-block checksums in the EXTENT_DATA item — was rejected by Btrfs designers on the grounds that EXTENT_DATA refs are shared (reflinks) and the checksum is a property of the physical block, not of the logical reference. Putting the checksum in the extent tree (one copy per physical block) is the only layout that preserves the "one checksum per physical block" invariant under arbitrary reflinking. NVFS should follow the same reasoning.

### 6.6 Scrub scheduling and progress

`btrfs scrub start [-B] [-r] [-d] <path>` starts a scrub; `status` reports progress; `cancel` aborts. Recommended cadence from the wiki: monthly on SSDs, weekly on large rotational arrays. The kernel remembers progress across mounts by writing a small state file under `/var/lib/btrfs/` (`btrfs-progs` side); a scrub interrupted by reboot resumes from where it left off. The on-disk impact of scrub is zero bytes written unless a repair is needed.

Progress is reported as `(bytes_scrubbed, bytes_total, data_extents_scrubbed, tree_extents_scrubbed, read_errors, csum_errors, verify_errors, no_csum, csum_discards, super_errors, malloc_errors, uncorrectable_errors, corrected_errors, last_physical)`. The fields are exposed by the `BTRFS_IOC_SCRUB_PROGRESS` ioctl for monitoring tools.

### 6.7 Dev-stat counters

Btrfs maintains per-device error counters, readable with `btrfs device stats <path>`: `write_errs`, `read_errs`, `flush_errs`, `corruption_errs`, `generation_errs`. Each increments in real time as the kernel sees errors; a monitor can poll this endpoint and raise an alert before scrub catches up. This is a deliberately minimal interface — the kernel does not parse or categorize the errors — and should be copied verbatim into NVFS.

## 7. Compression

Btrfs compresses at the **extent** level, transparently:

- Algorithms: zlib (levels 1–9), lzo (one level), zstd (levels 1–15 since kernel 4.14).
- Enablement: global mount option `compress=<alg>[:level]` or `compress-force=<alg>`; per-file `chattr +c`; per-directory inherited via xattr.
- Unit: one extent is one compressed chunk; max 128 KiB per compressed extent (`BTRFS_MAX_UNCOMPRESSED`).
- Detection: the kernel tries the configured algorithm on the first 128 KiB of the extent; if it fails to shrink below `128 KiB - PAGE_SIZE` the extent is stored uncompressed (unless `compress-force` is used).
- Interaction with CoW: a CoW rewrite of any byte in a compressed extent rewrites the whole extent (it must, because compression is non-incremental).
- Data is decompressed into the page cache on read and compressed on write; the fs tree's `EXTENT_DATA.compression` field pins the algorithm for that extent.
- Compression and encryption are mutually orthogonal (encryption is unimplemented — `EXTENT_DATA.encryption` reserves a byte).

Primary sources:
- `Documentation/filesystems/btrfs.rst` "Compression".
- `fs/btrfs/compression.c`.
- LWN "Btrfs zstd support," 2017-10, <https://lwn.net/Articles/729597/>.

### 7.1 Algorithm and level trade-offs

Btrfs's three compressor families are tuned for different speed/ratio spots:

- **zlib (DEFLATE):** levels 1–9. Level 3 is the historical default. Ratios of 2–3× on typical text/log data at ~80 MB/s compress, ~200 MB/s decompress on one modern core. Pure-Rust / pure-Simple implementations are plentiful.
- **lzo (LZO1X-1):** one level. About 300 MB/s compress, 600 MB/s decompress per core, at modest ratios (1.5–2×). Historical choice for speed.
- **zstd:** levels 1–15 in the kernel (upstream zstd supports 22, but Btrfs caps for memory). Level 3 is the default when `compress=zstd` is specified without a level. Levels 1–3 match or beat lzo on speed; levels 10+ approach zlib-9 ratios at lzo-like speeds. Zstd is the current recommended default.

The `compress-force=` variant skips the "did the algorithm shrink it?" check, writing compressed extents even when they are larger — useful for testing and for storage-class policies that prefer compression metadata overhead to block-level variability.

### 7.2 Compression interaction with reflink and CoW

When a file with a compressed extent is reflinked, both references point at the same compressed physical extent; they must use the same algorithm. A subsequent write to one side CoWs the *entire* compressed unit (up to 128 KiB) and decompresses, modifies, re-compresses — expensive relative to an uncompressed CoW of one block. For workloads with small random writes against reflinked data (copy-on-write container images), `chattr -c` on the hot region is often the right answer.

### 7.3 Compression and checksumming order

Btrfs checksums the **on-disk** (compressed) bytes, not the decompressed logical bytes. This is cheaper (less data to hash) and detects FTL-layer corruption of the compressed payload, but has a subtle consequence: a checksum mismatch on a compressed extent leaves the whole 128 KiB decompression block unrecoverable even if only one underlying compressed sector is bad. On RAID1 this is fine (the mirror fixes it); on `single` profile it is a correctness issue that scrub surfaces in `verify_errors`.

## 8. The log tree and fsync

`fsync(2)` on Btrfs is not a full transaction commit. A full commit would have to flush every dirty inode and every ancestor CoW across the tree forest; that is far too expensive for a per-file durability primitive. Instead, Btrfs maintains a **log tree** (`BTRFS_TREE_LOG_OBJECTID`) per subvolume that captures just the items needed to replay the fsynced changes on recovery.

The log tree is itself a normal B-tree; its root bytenr is written to the superblock's `log_root`. On crash:

1. Mount reads `super.log_root`.
2. If set, recovery walks the log tree per-subvolume, applying `LOG_ITEM`s that overwrite or add `INODE_ITEM`, `INODE_REF`, `EXTENT_DATA`, `DIR_ITEM`, `DIR_INDEX` entries in the target fs tree.
3. After all logs are replayed, the log tree is destroyed and the filesystem proceeds as consistent.

Entries in the log include **full-inode snapshots** for complicated cases (renames, directory reorganizations) and **partial updates** for simple appends. See `fs/btrfs/tree-log.c` for the state machine. The log is always a **redo** log — it never undoes; Btrfs relies on CoW for abort semantics.

Properties:

- Log is per-subvolume, but the `log_root` superblock field references the root **tree** holding all log tree roots, so a single superblock bump commits all logs.
- Log records do NOT carry full-data; they carry `EXTENT_DATA` items that reference extents already persisted in the main extent tree. fsync therefore has to complete data writes *before* writing the log record, exactly as ordered data mode mandates.
- On a normal commit, the log is truncated and a new one starts. There is no log-rotation in the Ext4 sense.
- `flushoncommit` forces a device flush before bumping the superblock (see §3.2). Disabling it weakens crash durability but not consistency.

Primary sources:
- `Documentation/filesystems/btrfs.rst` "Tree log".
- `fs/btrfs/tree-log.c`.
- LWN "The fsync wars," multiple installments, 2012 onward.

### 8.1 What the log captures

The tree log is deliberately **not** a general-purpose journal. It records exactly enough to let recovery rebuild the state that a successful `fsync(2)` promised. The kernel maintains a per-inode `log_list` that tracks which log updates are needed when that inode is fsynced next. On fsync:

1. If the inode has been renamed, deleted, or moved in a way that invalidates the log, a "full sync" is forced — the whole inode's content is relogged.
2. Otherwise, the delta since last fsync is appended to the log: new EXTENT_DATA items, updated INODE_ITEM, new INODE_REF / DIR_ITEM entries for directory operations.
3. The log-tree root is allocated and written, the log pointer in the superblock is updated, and the superblock is flushed.

On replay, the log entries are applied over the fs tree items they override. There is no undo step — the design relies on CoW immutability for the "before" state. Replay either completes or, on failure, leaves the log to be reported to the administrator via mount error.

### 8.2 Log corruption and `zero-log`

If the log tree itself is corrupted (torn write, media failure on the log extent), the mount fails with a clear error. The recovery path is `btrfs rescue zero-log <device>`, which clears `super.log_root` and lets mount proceed. Data loss is limited to the fsyncs since the last full commit — which, with the default 30 second commit interval, is bounded.

### 8.3 Log size

The log is small by design — typically hundreds of KiB to a few MiB per subvolume, because it is destroyed at every commit. Unlike ext4's or xfs's journal, there is no configurable log size, because the log never grows indefinitely.

## 9. Send and receive

### 9.1 Stream format

`btrfs send` writes a **TLV stream** of commands describing how to reconstruct a target state from an optional parent. The grammar is documented in `Documentation/btrfs-send-stream-format.rst`:

- Magic: 13 bytes `btrfs-stream\0`, followed by 4-byte version.
- Each command: `(u32 len, u16 cmd, u32 crc)` header, then a sequence of TLV attributes `(u16 type, u16 len, bytes[len])`.
- Core commands: `SUBVOL`, `SNAPSHOT`, `MKFILE`, `MKDIR`, `MKNOD`, `MKFIFO`, `MKSOCK`, `SYMLINK`, `RENAME`, `LINK`, `UNLINK`, `RMDIR`, `SET_XATTR`, `REMOVE_XATTR`, `WRITE`, `CLONE`, `TRUNCATE`, `CHMOD`, `CHOWN`, `UTIMES`, `UPDATE_EXTENT`, `END`, `FINISH`.
- `WRITE` attribute carries file offset + data bytes. `CLONE` carries source subvolume + source file + source offset + length — so send can express reflinks across the stream.

### 9.2 Incremental send

Given a parent read-only snapshot P and a new read-only snapshot C with `C's parent = P`, `btrfs send -p P C` walks the fs trees diff and emits only the `WRITE` / `RENAME` / etc. commands that move P's state forward to C's. The walk uses backref search on both subvolumes; it is O(changed items), not O(filesystem size). This is the reason Btrfs snapshots + send outperform rsync on large, slowly-changing filesystems.

The diff algorithm is described in Btrfs-progs `btrfs-progs/cmds/send-utils.c` and in Bacik's "Send/Receive for Btrfs" talks.

### 9.3 Receive

`btrfs receive` reads the TLV stream and executes the commands inside a target directory, which must contain an empty subvolume where the new snapshot will appear. Commands are applied in stream order; CLONE commands refer to already-received subvolumes (the receiver pins them) and to the current subvolume (for intra-snapshot sharing).

### 9.4 Security and authentication

The stream format does not authenticate the sender. If the bytes are altered in transit they will either fail a CRC check (per-command) or produce corrupt output; neither is a cryptographic guarantee. The Btrfs wiki explicitly says users who care about tamper-resistance must wrap the stream in a signed transport (GPG, SSH). A proposal for authenticated send streams exists on-list but is not merged as of kernel 6.11.

Primary sources:
- `Documentation/btrfs-send-stream-format.rst`.
- `btrfs-progs/cmds/send.c`, `btrfs-progs/cmds/receive.c`.
- LWN "Incremental backups with Btrfs send/receive," 2012-11, <https://lwn.net/Articles/506244/>.

### 9.5 Stream format versions

Version 1 is the original 2012 format; version 2 (merged for kernel 6.0) adds support for `ENCODED_WRITE` commands that preserve on-disk compression across send/receive. Without `ENCODED_WRITE`, a send of a zstd-compressed extent decompresses it into a `WRITE` command and the receiver re-compresses it (wasteful and lossy of specific compression choices). Version 2 streams therefore transfer less data on compressed filesystems and preserve the exact extent boundaries on the destination — important for maintaining reflink relationships through a send/receive cycle.

Compatibility: a receiver announces supported versions to the sender via a capabilities handshake; a version-2 sender can fall back to version-1 output when sending to an older receiver.

### 9.6 Relationship-preserving send

A read-only snapshot that was taken as a `btrfs subvolume snapshot -r /src /snap` preserves a "received UUID" field (`ROOT_ITEM.received_uuid`) on the receiver that maps the receiver's local snapshot to the source's UUID. Subsequent incremental sends from the source can reference this received UUID to pick up where the previous send left off without requiring the user to track snapshot parentage explicitly.

This is the piece that makes `btrbk`'s one-line backup config work: the tool does not need to track state files because the filesystem itself records the incremental history in received_uuid chains.

### 9.7 Security considerations

Send streams contain filesystem contents but do **not** contain filesystem structure — no raw bytenrs, no tree keys, no direct device references. A send is therefore portable across machines with different Btrfs layouts. However, the stream is not authenticated, as noted above, and a man-in-the-middle can alter commands. The practical recommendations from the Btrfs wiki:

- Pipe through SSH for authenticated transport: `btrfs send ... | ssh host btrfs receive /target`.
- Verify the destination snapshot's `received_uuid` matches the source's UUID after receive.
- Use read-only snapshots on both sides as integrity checkpoints.

### 9.8 Failure modes

A partial send (connection lost mid-stream) leaves the destination with a **partial** subvolume that is marked incomplete. The receiver will not promote the partial subvolume to readable — a subsequent `btrfs subvolume list` shows it but with a flag indicating incomplete receive. The user must delete it and retry.

## 10. Recovery and integrity

### 10.1 Mount-time recovery

A normal mount:

1. Reads the highest-generation valid superblock on each device.
2. Loads the chunk tree (bootstrapping from the superblock's `system_chunk_array`).
3. Loads the root tree.
4. Loads the extent tree, fs tree, csum tree, device tree, (uuid/free-space/block-group/quota/raid-stripe trees if present).
5. Replays the log tree if `super.log_root` is non-zero (see §8).
6. Marks the filesystem mounted.

### 10.2 `btrfs check`

`btrfs check` (`btrfs-progs/check/main.c`) is the offline fsck:

- Walks the entire extent tree, cross-checking against every referenced fs tree and the chunk tree.
- Verifies refcounts, backrefs, inode link counts, dir indexes, csum coverage.
- Has a `--repair` mode whose warning label reads in caps in the manpage and the wiki: "Do not use --repair unless a Btrfs developer tells you to." The wiki reinforces that `--repair` can make damage worse. The preferred recovery starts with `--readonly` plus `btrfs rescue`.

### 10.3 `btrfs rescue`

A family of narrow repair tools:

- `btrfs rescue chunk-recover` — rebuilds the chunk tree from dev_extent scans when the chunk tree is corrupted.
- `btrfs rescue super-recover` — copies one good superblock copy onto the others.
- `btrfs rescue zero-log` — wipes a corrupted log tree (data loss of post-last-commit fsyncs).
- `btrfs rescue fix-device-size` — fixes device size mismatches.
- `btrfs restore` — reads files out of an unmountable filesystem to a different destination, without attempting to fix the source. This is the documented "first response" for ENOSPC'd or block-group-corrupted filesystems.

Primary sources:
- `btrfs-progs/Documentation/btrfs-check.rst`.
- `btrfs-progs/Documentation/btrfs-rescue.rst`.
- Btrfs wiki "Problem FAQ".

### 10.4 Barriers and durability

Btrfs relies on `REQ_PREFLUSH | REQ_FUA` (or `REQ_FUA` alone where the device supports write-through on a per-I/O basis). The `nobarrier` mount option disables both flushes in the commit path; the docs warn that this is unsafe on any storage that does not itself guarantee commit ordering (i.e. almost all of it). The `flushoncommit` mount option (default: on) is the specific flush bracketing described in §3.2.

On ZNS / zoned block devices (`-o zoned`), Btrfs performs all writes as zone-append and relies on the device's explicit zone-append ordering instead of preflush; see `Documentation/filesystems/btrfs.rst` "Zoned devices".

### 10.5 The ENOSPC conundrum

Btrfs's historical ENOSPC bugs deserve their own discussion. A CoW filesystem that needs free space to free space (deleting a file requires writing CoW-updated metadata that points at the old file as freed) can wedge itself if free-space tracking is imprecise. Modern kernels (5.x onward) have largely tamed the issue via the global block reserve, delayed-ref accounting, and `btrfs_reserve_metadata_bytes` gating, but "ENOSPC at 80 % full" remains a possible failure mode under extreme metadata growth (e.g. millions of small files, deep snapshot stacks).

Recovery approaches, in order of increasing disruption:

1. Add a device temporarily: `btrfs device add /dev/loopN /mnt && btrfs balance start ... /mnt` then remove it.
2. Delete unused snapshots: many ENOSPC reports come from someone with thousands of unused snapshots.
3. Remount with `rescue=clear_cache` to rebuild the free-space tree.
4. Use `btrfs rescue` or `btrfs restore` to copy out data.

The lesson for NVFS: **always** reserve metadata for the current operation before mutating any on-disk state. This rule, applied consistently, prevents the ENOSPC wedge.

### 10.6 Backup roots and `usebackuproot`

Each superblock carries a small array of "backup roots" — the last few committed root-tree and chunk-tree pairs. If the current root is unreadable, `-o rescue=usebackuproot` tries each previous root in turn, looking for one that mounts. This is an invaluable recovery mode; the cost is four extra 64-byte entries per superblock commit, which is negligible.

NVFS should unreservedly adopt this: the superblock's capacity for multiple historical roots turns most "corrupted root tree" failures into "mount with the previous generation and restore" — a vastly easier recovery story than going straight to offline fsck.

## 11. Quotas and qgroups (brief, not core to the port)

Btrfs's quota system is not per-user/per-group like POSIX quotas but per-**qgroup** — a hierarchy of quota groups that can track subvolumes. Enabling quotas creates the quota tree (`BTRFS_QUOTA_TREE_OBJECTID`). qgroups track **exclusive** and **shared** bytes per subvolume; the accounting is kept up to date by observing delayed-ref updates during commit.

Known issues (documented in `Documentation/filesystems/btrfs.rst`):

- Quota rescan can be very expensive after deleting large snapshots.
- Enabling quotas on a large filesystem can take hours for the initial rescan.
- qgroup enforcement is best-effort at deep subvolume trees.

For NVFS this is almost entirely SKIP — the use cases (container management, per-tenant billing) can be expressed above the filesystem via arena-level accounting.

### 11.1 Qgroup hierarchy

Qgroups are identified by a 64-bit id of the form `level:objectid` — level 0 qgroups correspond one-to-one to subvolumes, and higher-level qgroups are containers that aggregate lower-level qgroups via `QGROUP_RELATION` items. Enforcement is per-qgroup: a write that would push any ancestor qgroup over its limit is rejected with `EDQUOT`.

Accounting requires tracking *exclusive* bytes (only this qgroup references them) separately from *shared* bytes (referenced by multiple qgroups via snapshots or reflinks). The shared-bytes bookkeeping is what makes qgroup rescan expensive — it must walk the extent tree cross-referencing backrefs.

### 11.2 Known limitations

From the Btrfs docs and list traffic:

- Deleting a large snapshot forces a rescan; during the rescan, qgroup numbers are inaccurate.
- Qgroups do not count metadata toward limits by default (configurable via `QGROUP_LIMIT.flags`).
- Squota (a simpler variant that tracks only exclusive bytes, skipping cross-reference accounting) is a proposed alternative but not merged as of 6.11.

These limitations explain why the Btrfs community has largely moved to expressing multi-tenant isolation via subvolumes + userland quotas (cgroups v2 `io.max`, per-directory project quotas via `chattr +P`) rather than qgroups. NVFS should skip qgroups outright.

## 12. Allocator and space management

### 12.1 Block groups

The allocator works on **block groups**, each of which owns one chunk (see §2.5). A block group has a type bitmap matching the chunk type (DATA | METADATA | SYSTEM, plus profile bits). Metadata and data live in separate block groups by default (`mixed-bg` puts them together but is recommended only for small filesystems, see mkfs manpage).

`BLOCK_GROUP_ITEM` used to live in the extent tree; since kernel 6.1 they can live in the dedicated block-group tree (`BTRFS_BLOCK_GROUP_TREE_OBJECTID`, incompat feature `BLOCK_GROUP_TREE`). The block-group-tree format cuts mount time on large filesystems by a factor of 10x to 100x because the extent tree no longer has to be scanned linearly for BLOCK_GROUP_ITEMs — see the LWN Oct 2022 article and Johannes Thumshirn's LSFMM 2022 slides.

### 12.2 Free-space tracking

Btrfs has had three free-space mechanisms:

- **v1 `space_cache`** — a hidden file per block group storing a compact "extent + bitmap" free-space representation. Loaded at mount, mutated in memory, rewritten on commit. Scales poorly past a few hundred GB.
- **v2 free-space tree** (`FREE_SPACE_TREE` compat_ro, `FREE_SPACE_TREE_VALID` subordinate compat_ro) — a dedicated B-tree keyed by `(block_group_offset, FREE_SPACE_EXTENT | FREE_SPACE_BITMAP, length)`. Kernel commit that introduced it: `a5ed9182a629` (2015). LWN writeup: <https://lwn.net/Articles/663021/>.
- **no cache** (`nospace_cache` mount option) — force a full free-space scan at mount of each block group; only practical on very small filesystems.

The FS-tree-v2 (`free-space-tree`) is the default on mkfs.btrfs since 5.15. It is written in the same commit as other trees and is consistent by construction; it does not need the post-crash re-generation that space_cache_v1 needed.

### 12.3 Allocation policy

`fs/btrfs/extent-tree.c:find_free_extent` searches block groups for the best-fit (small allocations) or a "cluster" (large streaming). Policies:

- **SSD**: `ssd` mount option changes the policy to prefer big contiguous allocations, minimizing FTL garbage collection. This is auto-detected for rotational=0 devices.
- **Discard**: `discard=async` (the default since 5.6 for `discard` aware setups) queues TRIM/UNMAP commands after extent freeing, batched and rate-limited; `discard=sync` does it inline; `nodiscard` does not discard at all. The trade-off is well-documented: `async` is almost always right for SSDs, because synchronous discard blocks metadata ops on some drives.
- **Cluster**: A cluster is a contiguous span of a block group reserved for a particular writer. Data clusters are 256 KiB; metadata clusters are 32 KiB. Clusters avoid fragmentation at the cost of small up-front over-reservation.

### 12.4 NVFS note

NVFS's own allocator is arena-based and already distinguishes storage classes. The Btrfs allocator's most load-bearing idea — per-block-group bookkeeping with class-aware search — maps almost directly to NVFS arena families. The free-space-tree-v2 concept (a dedicated tree updated inside the same commit) is a candidate KEEP for NVFS.

Primary sources:
- `fs/btrfs/extent-tree.c:find_free_extent`.
- `Documentation/filesystems/btrfs.rst` "Free space tree", "Discard".
- LWN "Free space tree," 2015-11, <https://lwn.net/Articles/663021/>.
- LWN "Btrfs block-group tree," 2022-10, <https://lwn.net/Articles/899810/>.

### 12.5 The `autodefrag` mount option

`autodefrag` watches for small random writes (signature of databases) and queues a background defragmentation that rewrites the affected ranges into contiguous extents. The knobs are fixed: a write is considered a candidate for defrag if it is smaller than 64 KiB and falls in a range containing more than a configurable number of small extents.

The option is not the default because defrag breaks reflink sharing (see §5.4). Any workload that cares about snapshot-driven dedup must leave autodefrag off. NVFS can expose the same option but should bind its documentation to the reflink-breaking caveat.

### 12.6 Bitmap vs extent free-space representation

Each block group's free space is represented either as a list of `FREE_SPACE_EXTENT` items (one per contiguous free region) or a `FREE_SPACE_BITMAP` item covering a fixed-size range with one bit per sector. Extent representation is optimal when free space is in a few large regions; bitmap is optimal when it is scattered across many small regions. The kernel switches between them per-block-group based on observed fragmentation, and the switch is a single commit operation.

A bitmap item covers 256 KiB of block-group space per byte (for 4 KiB sectors). A fully-bitmap-encoded 1 GiB block group takes 32 KiB of bitmap data plus header overhead — small enough to fit in a single 16 KiB leaf twice.

### 12.7 Allocation cluster policy

`btrfs_find_cluster` (`fs/btrfs/free-space-cache.c`) implements cluster-based allocation. A cluster is a pre-reserved contiguous span within a block group, intended to serve many small allocations in order without re-searching. Clusters exist per-(block group, metadata/data) tuple:

- **Metadata cluster:** 32 KiB, enough for two node-sized blocks.
- **Data cluster:** 256 KiB, enough for 64 contiguous 4 KiB writes.

The allocator first tries the current cluster; if it is exhausted or fragmented, a new cluster is carved out of the best contiguous free-space region in the block group; if none is large enough, the cluster policy is bypassed and individual free-extents are consulted directly. This gives a 2-level optimization: common case O(1), rare case O(log N).

### 12.8 Chunk preallocation vs per-write allocation

Btrfs preallocates chunks opportunistically. When free space in existing chunks drops below a threshold, the next commit allocates a new chunk proactively rather than waiting for the allocator to fail. The threshold and preallocation size are adaptive: large filesystems preallocate 1 GiB chunks, small filesystems 256 MiB or smaller. The goal is to avoid "allocation stalls" where a write must wait for chunk creation.

This is a frequent source of confused "why is my Btrfs using 5 GiB when I've written 2 GiB?" questions, and the reason `btrfs filesystem usage` is more informative than `df`. NVFS should either copy the preallocation policy and expose the same diagnostic commands, or document clearly that arena families do not preallocate.

## 13. Balance and relocation

### 13.1 Relocation = CoW rewrite of a block group

`btrfs balance` is how Btrfs reshapes itself online. The operation:

1. Takes a set of filter expressions that pick which block groups to rewrite (`profiles=`, `usage=`, `vrange=`, `devid=`, `drange=`, `limit=`, `convert=`, `soft`).
2. For each chosen block group, uses the **relocation tree** mechanism to rewrite every extent in it elsewhere and free the original.
3. Updates backrefs in every fs tree that pointed at the old extents.
4. Deletes the empty block group and its chunk.

Step 2 is the key part. `fs/btrfs/relocation.c` builds a **relocation tree** that mirrors the structure of each fs tree being touched, with new extents as leaves. It then swaps the relocation tree into place — transactional, all-or-nothing.

Uses:

- **Device removal** (`btrfs device delete <dev>`) — relocate all chunks on that device elsewhere, then release.
- **Profile conversion** (`btrfs balance -dconvert=raid1 -mconvert=raid1c3 /mnt`) — rewrite chunks into the new profile.
- **Fragmentation / small-block-group compaction** — merge several half-empty block groups into fewer full ones (the `usage=` filter).
- **Defrag of metadata** — indirectly, because CoW rewrite bumps locality.

Balance is reversible per-commit: if it crashes, the next mount finds the half-copied blocks as unreferenced and frees them. Any extent already referenced by the relocation tree but not yet swapped remains reachable from the original fs tree.

### 13.2 Online resize

`btrfs filesystem resize` grows or shrinks a device. Shrink uses the relocation machinery to move any block groups off the soon-to-be-gone tail; grow just bumps the device-size field.

### 13.3 Device replace

`btrfs replace` is a faster device-migration than "balance + delete". It streams the contents of the source device to the target, and **after completion** swaps the dev_item in the chunk tree. During the replace, reads from stripes on the source device also write to the target in one I/O.

Primary sources:
- `fs/btrfs/relocation.c`.
- `Documentation/filesystems/btrfs.rst` "Balance", "Device replace".
- LWN "Btrfs: Working with multiple devices," 2014, <https://lwn.net/Articles/577961/> and follow-ons.

### 13.4 Balance filters and semantics

Balance is exposed to users via filters that select a subset of block groups to rewrite:

- `profiles=single|raid0|raid1|raid1c3|raid1c4|raid10|raid5|raid6|dup` — pick block groups with this profile.
- `usage=<n>` or `usage=<min>..<max>` — pick block groups whose utilization falls in the range (0–100 %). `usage=0` picks empty block groups to free them; `usage=50` picks half-full ones to merge.
- `devid=<id>` — pick block groups with a stripe on this device.
- `drange=<start>..<end>` — pick block groups whose physical address overlaps this range (for recovering physical regions).
- `vrange=<start>..<end>` — same but in logical address space.
- `limit=<n>` or `limit=<min>..<max>` — cap the number of block groups processed.
- `stripes=<n>..<m>` — pick by stripe count (used for RAID6 with specific geometry).
- `soft` — skip block groups already in the target profile (idempotence).
- `convert=<profile>` — change the profile while rewriting.

A common recipe: `btrfs balance start -dusage=50 -musage=30 /mnt` — reclaim half-empty data and mostly-empty metadata chunks. This is the "Btrfs maintenance cron" default.

The relocation tree is a mirror of each fs tree being updated by the balance, but with new bytenrs for the rewritten blocks. The swap-in step atomically replaces the fs-tree root with the relocation-tree root inside a single transaction. Any read that races the swap sees either the old root (and reads from the old extents, which are still alive) or the new root (and reads from the new extents). Neither case sees a partial swap.

### 13.5 Balance pause / resume

`btrfs balance pause /mnt` and `btrfs balance resume /mnt` checkpoint the balance state. On a crash or unclean unmount during balance, the next mount automatically resumes the balance from the last checkpoint (or, with `skip_balance` mount option, refuses to resume for debugging). Between checkpoints, all state is on-disk; the checkpoint is just the progress marker.

## 14. Mount options and defaults (correctness knobs)

This section lists the mount options with correctness implications, not the tuning knobs. Source: `Documentation/filesystems/btrfs.rst` "Mount options" and `btrfs(5)` manpage.

| Option | Default | Effect |
|---|---|---|
| `datacow` / `nodatacow` | datacow | Disable CoW for writes; implies `nodatasum`; breaks snapshot semantics for first write after snapshot. |
| `datasum` / `nodatasum` | datasum | Disable checksumming of data (metadata is always checksummed). |
| `barrier` / `nobarrier` | barrier | Disable device-cache flushes at commit. Unsafe on almost all consumer SSDs. |
| `flushoncommit` / `noflushoncommit` | flushoncommit | Disable the double REQ_PREFLUSH bracket around the commit. Corruption-prone. |
| `space_cache=v1|v2` / `nospace_cache` | v2 (since 5.15) | Which free-space representation to use; `nospace_cache` forces scans. |
| `discard=async|sync|no` | async on capable drives | TRIM/UNMAP policy. |
| `ssd` / `nossd` / `ssd_spread` | auto | Allocator biases for SSDs. |
| `compress=<alg>[:level]` / `compress-force=<alg>` / `compress=no` | off | Per-mount compression. |
| `autodefrag` / `noautodefrag` | noautodefrag | Background defrag of small random-write files (databases). |
| `enospc_debug` | off | Verbose enospc failure traces. Developer option. |
| `subvol=<path>` / `subvolid=<id>` | default subvol | Which subvolume to mount. |
| `rescue=usebackuproot,nologreplay,ignorebadroots,ignoredatacsums,all` | off | Emergency mount modes. Explicit, not default. |
| `zoned` | auto on zoned devs | Select zoned-append I/O path. |

The "default safe" set is: `datacow`, `datasum`, `barrier`, `flushoncommit`, `space_cache=v2`, `discard=async`. Documented defaults; they are what mkfs produces.

### 14.1 Rescue mode details

`-o rescue=<list>` combines one or more emergency flags:

- `usebackuproot` — try the superblock's backup roots in order when the main root is unreadable.
- `nologreplay` — skip log replay on mount; useful when the log tree is the corrupted piece.
- `ignorebadroots` — skip subvolumes whose fs-tree root is unreadable rather than failing the mount.
- `ignoredatacsums` — disable data checksum verification (but not write, so the tree stays consistent).
- `all` — the shorthand that enables all of the above.

These are **not** long-term mount flags. The documented workflow is: mount with `rescue=all` read-only, copy what you can, then fix the filesystem offline with `btrfs check --repair` under developer guidance or wipe and restore from backup.

### 14.2 Mount option interactions

Some mount options are exclusive or imply others:

- `nodatacow` forces `nodatasum` for affected inodes.
- `compress-force` overrides per-inode `compress=no`.
- `nobarrier` with `flushoncommit` still flushes at commit but skips per-I/O barriers; this combination is rarely sensible.
- `autodefrag` plus many reflinks is a footgun (§12.5).
- `space_cache=v1` plus a snapshot-heavy workload is slow; v2 is strongly recommended.

NVFS should refuse invalid combinations at mount time and emit a clear error message — a lesson from Btrfs's historical tolerance of near-nonsense option combinations that led to silent misbehaviour.

### 14.3 Remount semantics

Some options can only be set at mount, some at both mount and remount, and a few can be cleared by remount. The Btrfs man page is the authoritative list. Relevant examples:

- `compress=<alg>` can be changed by remount; already-written extents keep their old algorithm. New extents use the new algorithm.
- `space_cache` version changes require a full unmount; switching from v1 to v2 clears the v1 cache at next mount.
- `nobarrier` on a mounted filesystem is accepted but the docs warn that barrier state within a commit cycle is undefined.
- `ro` to `rw` remount requires a clean log (or `rescue=nologreplay` to bypass).

NVFS should explicitly enumerate which options are remountable and which are mount-time-only, rather than leaving it to users to discover by experiment.

## 15. Benchmarks and tradeoffs vs ext4, xfs, zfs (brief)

Primary sources are intentionally varied here because no vendor-neutral benchmark of filesystem performance ages well:

- **Phoronix** runs roughly annual filesystem benchmarks; the 2023 results (ext4 vs xfs vs btrfs vs f2fs, <https://www.phoronix.com/review/linux-614-filesystems>) show Btrfs trailing ext4/xfs on small-file random writes by roughly 20–40 %, leading on workloads that exercise snapshotting, and being competitive on large sequential I/O with compression on.
- **Facebook's** btrfs deployment notes (Josef Bacik, LSFMM 2019 <https://lwn.net/Articles/787064/>): ~10 % throughput cost for CoW + checksums was acceptable in exchange for the operational win of cheap snapshots.
- **Oracle** tech brief <https://docs.oracle.com/en/operating-systems/oracle-linux/8/fsadmin/fsadmin-UsingtheBtrfsFileSystem.html> is a neutral operations summary.
- **ZFS comparison**: ZFS has a similar CoW model, more mature RAID5/6 equivalent (RAIDZ), per-pool rather than per-block-group RAID, mandatory full volume membership at pool creation, and a heavier memory model (ARC). Btrfs's per-chunk RAID and per-subvolume CoW are the opposite choice: more flexibility, less per-IO parallelism.
- **xfs comparison**: xfs is not CoW except for `reflink=1` (since 2018); xfs reflinks are real but snapshots and checksums are not a first-class feature.
- **ext4 comparison**: No CoW, no snapshots; journaling is metadata-only by default; fastest small-file performance among the four.

The general trade-off Btrfs makes: **trade per-operation throughput for per-dataset flexibility**. NVFS's target audience is closer to Btrfs's than ext4's — we care more about cheap snapshots and integrated checksums than about peak random-write IOPS.

### 15.1 Specific workload comparisons

Taken from the public Phoronix 2023 suite, Bacik's LSFMM 2019 talk, and vendor notes:

- **Sequential write, 4 KiB blocks, no compression.** ext4 and xfs roughly 1.0× (baseline), Btrfs 0.85–0.90× due to CoW overhead. With compression on, Btrfs pulls ahead by 1.5× on compressible data because there is less to write.
- **Random 4 KiB write.** ext4/xfs 1.0×, Btrfs 0.6–0.8× due to CoW write amplification and metadata pressure. This is the workload where `nodatacow` (disabling CoW for the affected file) makes the biggest difference.
- **Small-file create (make a million files).** ext4 leads, xfs close, Btrfs roughly 0.7× due to metadata tree CoW. Block-group tree (6.1+) closes about half the gap.
- **Snapshot creation.** ext4/xfs have no comparable feature. Btrfs and ZFS both O(1).
- **Snapshot delete of a diverged snapshot.** Btrfs background cleaner, minutes to hours depending on size. ZFS similar. ext4 has no feature.
- **Checksum verification on read.** Btrfs ~3–10 % overhead on cold reads, ~1 % on warm reads. ext4 has no comparable feature; xfs optional V5 metadata checksums but no data checksums.
- **Mount time on a 10 TiB filesystem.** ext4/xfs typically sub-second. Btrfs without block-group tree: minutes to tens of minutes. With block-group tree (6.1+): a few seconds.
- **`fsync` latency.** Btrfs's tree log typically beats ext4's full journal commit by 20–40 % under contention, but can regress on complex rename cases where Btrfs forces a full sync.

### 15.2 Why Btrfs is still a compelling model for NVFS

Despite the performance gaps, Btrfs continues to be chosen for production (Meta's rootfs, SUSE's default rootfs, Synology's NAS filesystem, Fedora's default since 33) because the non-performance properties matter more for those use cases: data integrity, cheap snapshots, send/receive replication, online device management. NVFS is pursuing the same value proposition — we therefore can and should accept the same order of performance compromise and spend engineering effort on the features, not on chasing ext4's raw throughput.

## 16. NVFS translation: KEEP / ADAPT / SKIP / ATTACH

NVFS reminder: the **virtual storage classes** are `META_DURABLE`, `DB_WAL`, `DB_TEMP`, `MODEL_IMMUTABLE`, `GENERAL_MUTABLE`, `CHECKPOINT_SNAPSHOT`. The `arena_*` API mediates all I/O. The **capability-probe table** is the registry of optional device-assisted features (NVMe ZNS, FDP, Copy, KV, CMB, PMR) that the runtime can switch on when present.

Legend: **KEEP** = adopt directly. **ADAPT** = keep the concept, change the mechanism. **SKIP** = do not port. **ATTACH** = surface as a capability in the probe table, optional by default.

### 16.1 Layout

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| Superblock with N copies at fixed offsets | KEEP | Three copies at `0x10000`, `0x4000000`, `0x4000000000` are a known-good discipline; map them onto `META_DURABLE`. |
| Superblock rotation with generation | KEEP | Generation counter matches NVFS's arena publish counter idea in `sys_pmap_publish`. |
| Tree forest | ADAPT | NVFS uses a flat pmap-per-class model. The forest idea maps to "one arena-root per class" rather than one tree per info-kind. For metadata, at least two classes — META_DURABLE (the catalog) and CHECKPOINT_SNAPSHOT (point-in-time views) — should have independent roots. |
| `(objectid, type, offset)` key | ADAPT | NVFS addresses by `(class, logical_extent_id, offset)`. The three-part key's sortability wins (range scans of per-object metadata) are worth keeping. |
| Node / leaf layout with per-block CRC32C | KEEP | Every metadata block must carry its own checksum. Use blake2b-256 by default (cryptographic, fast) with CRC32C as the capability-probe fallback for CPUs without SIMD. |
| `SKINNY_METADATA` | ATTACH | Compact metadata-extent encoding is a minor optimization; attach to the probe table as a write-side feature, disabled until a real win is measured. |
| Chunk tree as logical↔physical map | ADAPT | NVFS already has the arena-to-LBA map. Adopt the per-chunk profile idea: an arena's RAID/redundancy choice is a field of the arena descriptor, not a filesystem-wide setting. |
| RAID profiles (single / DUP / RAID0 / RAID1 / RAID1C3 / RAID1C4 / RAID10) | ADAPT | NVFS should start with `single` and `mirror(n)` where n=2,3,4; naming should avoid "RAID1 = 2 copies" ambiguity by always requiring the copy-count explicitly (`mirror=3`, not `raid1c3`). Per-class default: DB_WAL=mirror-2 minimum, META_DURABLE=mirror-3 minimum. |
| RAID5/RAID6 with write hole | SKIP for v1, ATTACH for v2 | Do not ship parity RAID until NVFS can mirror Btrfs's zoned-RAID-stripe-tree design (LWN 2023+) or provide an explicit stripe journal. The write hole is a real loss-of-data event under plausible workloads. |
| EXTENT_DATA with `(disk_bytenr, disk_num_bytes, offset, num_bytes)` split | KEEP | This is the cleanest shared-extent encoding known. NVFS's `BlobRef` concept already approaches this; adopt the exact four-field layout. |
| Back-references in the extent tree | KEEP | Offline fsck and scrub are impossible without them. NVFS's arena is append-only but its extents are still refcounted; per-extent backref chain is a small fixed add-on. |

### 16.2 CoW model

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| Shadowed CoW B-tree (Rodeh) | KEEP | NVFS's pmap publish is already a shadow-atomic operation; treat all metadata as CoW by rule, not by option. |
| Transaction groups with generation number | KEEP | Our existing `sys_pmap_publish` writes the new root atomically; adopt Btrfs's convention of putting the generation in every block header so mirror staleness is obvious. |
| Commit pipeline (ordered data → metadata → superblock with double flush) | KEEP | Ordered data is the only rule under which per-inode fsync is meaningful without a full WAL copy of data. NVFS inherits this automatically because its arenas are append-only, but the double-flush on superblock publish is an explicit KEEP. |
| Space reservation ("reserve before mutate") | KEEP | NVFS needs a `reserve_metadata_bytes`-equivalent to avoid ENOSPC mid-operation. This is the failure mode that has taken the most kernel-years to fix in Btrfs; do not rediscover it. |
| `flushoncommit` | KEEP as default on | Expose as a mount option; default on. |
| `nobarrier` | SKIP | Do not expose. The small performance win is not worth the correctness risk on any consumer device. |

### 16.3 Snapshots and reflinks

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| Subvolume = independent tree root | ADAPT | NVFS already has `CHECKPOINT_SNAPSHOT` as a storage class. Redefine a "checkpoint" as a root entry in META_DURABLE pointing at a frozen snapshot of the other classes; this matches Btrfs subvolume semantics. |
| Snapshot = writable clone of a subvolume | ADAPT | NVFS CHECKPOINT_SNAPSHOT is read-only by construction; to get writable snapshots we need the same mechanism with a new mutable fs-tree pointer. Plan this for after the read-only MVP. |
| Ref-counted shared tree blocks | KEEP | Rodeh 2008 is the definitive paper on this; NVFS should implement it as described, with backrefs. |
| Reflink (`FICLONE`, `FICLONERANGE`) | KEEP | Essential for `cp --reflink`, container layer dedup, and snapshot-as-CoW-copy. |
| `FIDEDUPERANGE` / EXTENT_SAME | ATTACH | Implement the ioctl but gate it behind an "out-of-band dedup" capability; keep the discovery side entirely in userspace, per the Btrfs pattern. |
| In-band dedup | SKIP | Btrfs's experience says this is not worth the commit-pipeline complexity for the typical block-dup rates on modern data. |

### 16.4 Self-healing and checksums

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| CRC32C default | ADAPT | Default to **blake2b-256** on NVFS (stronger than CRC32C; faster than SHA-256 on common CPUs). Capability-probe CRC32C as a cheap alternative for META_DURABLE hot-path on SIMD-poor CPUs. |
| Separate checksum tree for data | KEEP | Data checksums as a separate index are the right design. In NVFS terms, this is a `META_DURABLE` index keyed by `(class, extent_id, offset)`. |
| Per-metadata-block inline checksum in header | KEEP | Metadata reads are latency-sensitive; inline checksum is the only acceptable layout. |
| Transparent repair on mirrored data | KEEP | The detect-on-read + pull-from-mirror + write-back mechanism is exactly what NVFS needs; no redesign required. |
| Scrub | KEEP | NVFS's arena model makes scrub trivially parallelizable across arenas; adopt Btrfs's per-device scrub worker model, translated to per-arena. |
| `nodatasum` / `nodatacow` | ATTACH | Expose as inode flags for large in-place-mutated files (VM images, big databases), with a big warning. Default is always on. |

### 16.5 Compression

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| Per-inode / per-mount compression (zlib / lzo / zstd) | ATTACH | NVFS supports `GENERAL_MUTABLE` and `MODEL_IMMUTABLE`; compression is especially valuable on the latter. Default algorithm: zstd level 3 (matches Btrfs default). Disable on DB_WAL (latency-sensitive). |
| Compression pre-filter (try-shrink-or-skip) | KEEP | Avoids wasting CPU on incompressible data. |

### 16.6 Send / receive

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| TLV stream format | ADAPT | NVFS should define its own stream format keyed to the class-based layout; Btrfs's TLV design is the right template. |
| Incremental send with parent snapshot | KEEP | Same algorithm: diff two frozen roots, emit only changes. |
| CLONE commands in the stream | KEEP | Preserves reflinks across send/receive, which is a major win for backup storage utilization. |
| Unauthenticated stream | ATTACH | Build-in optional HMAC or signature from v1; Btrfs's "wrap it in SSH" posture is not defensible for a new filesystem in 2026. |

### 16.7 Recovery and integrity

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| Per-subvolume log tree for fsync | ADAPT | NVFS's `DB_WAL` class already carries the concept. Make the per-class log an explicit arena, replayed at mount. |
| `btrfs check` offline fsck | KEEP | A full offline checker is non-negotiable for anyone trusting production data to NVFS. |
| `btrfs rescue` toolkit | KEEP | Specifically: super-recover, chunk-recover, zero-log, restore. These are the set that solves "my filesystem wedged" most of the time. |
| Barrier / flush discipline | KEEP | Same as §16.2. |
| `rescue=usebackuproot,nologreplay,ignorebadroots,ignoredatacsums` mount modes | ATTACH | Debug-only, off by default, surfaced explicitly. |

### 16.8 Quotas

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| qgroups | SKIP | NVFS's arena-level accounting is more natural for our deployment. |

### 16.9 Allocator

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| Block groups with per-group type/profile | KEEP | Matches NVFS arena-with-policy model; already how we think. |
| Free-space tree v2 (in-band tree updated in commit) | KEEP | v1 space_cache's post-crash revalidation cost is the cautionary tale; start with v2-equivalent. |
| Clusters (reserved large contiguous spans) | KEEP | Tiny code, big locality win on streaming writes. |
| `ssd` auto-detect | KEEP | Same heuristic. |
| `discard=async` default | KEEP | The default matches NVMe realities. |
| Block-group tree (incompat) | KEEP for v1 | Put block-group items in their own index from day one; don't repeat the Btrfs-era "mount time grew linearly with FS size for a decade" mistake. |

### 16.10 Relocation / balance

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| `balance` as online chunk rewrite | KEEP | Online device removal, profile conversion, and fragmentation-compaction are the table stakes for a modern filesystem. |
| Relocation tree | KEEP | The mechanism is elegant and known to be correct. |
| Online resize | KEEP | Trivial given the above. |
| `replace` for fast device migration | KEEP | Streaming copy with in-flight dual write is the cheap win. |

### 16.11 Mount options / defaults

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| `flushoncommit`, `discard=async`, `space_cache=v2`, `ssd` | KEEP as defaults | Match Btrfs's safe set. |
| `nodatacow`, `nodatasum`, `nobarrier`, `noflushoncommit` | SKIP or ATTACH | Dangerous footguns; expose only with explicit opt-in and doc warnings. |

### 16.12 Zoned / NVMe-aware

| Btrfs feature | NVFS action | Notes |
|---|---|---|
| `zoned` mount with zone-append | KEEP | NVFS already capability-probes ZNS; Btrfs's zoned code is the nearest production example of this path. |
| RAID-stripe tree for zoned RAID | ATTACH | Track upstream; when NVFS gets parity RAID, copy the stripe-tree design rather than reinventing. |

## 17. Open questions for NVFS design update

1. **Checksum algorithm default.** Btrfs ships CRC32C as default; NVFS plans blake2b-256. Confirm the CPU-cost budget on the slowest target (baremetal Simple-OS on entry-level x86_64) is acceptable, and keep a CRC32C probe fallback.
2. **RAID1 naming.** Btrfs's "RAID1 = 2 copies" vs "RAID1C3 = 3 copies" has been a perennial support nightmare. NVFS should pick a naming scheme now (`mirror=n`?) and document it with the same care as POSIX.
3. **Log tree vs WAL class.** NVFS has a `DB_WAL` storage class; the question is whether to reuse it for filesystem-metadata logging (fsync log) or keep the fs log in `META_DURABLE` and reserve `DB_WAL` for above-NVFS clients (spostgre). The cleanest answer is probably "both, but at separate arena-descriptor keys."
4. **Subvolume objectid space.** Btrfs reserves objectids < 256 for trees. NVFS should do the same for arena descriptors so future trees can be added without collision.
5. **Backref chain storage.** Does NVFS encode backrefs inline in the extent item (Btrfs's `EXTENT_ITEM_KEY` + inline refs) or in a separate index? Btrfs went with inline for compactness but paid in complexity; given we are starting fresh, an external index is simpler.
6. **qgroup support.** Do we want per-subvolume accounting at all, or is arena-level usage sufficient? (Recommendation: arena-level only.)
7. **Authenticated send stream.** MAC vs signature vs "don't bother, wrap in TLS"? Btrfs deferred this; we should decide up front.
8. **In-band dedup.** Chris Mason's 2013 RFC never merged. We should write an explicit non-goals statement to avoid the pressure to attempt it.
9. **Mixed block groups.** Btrfs supports DATA and METADATA in one block group (`-M`). Given NVFS's class design, is there a case where we would want to mix?
10. **Relocation tree vs arena-level move.** Is a user-visible balance command valuable, or are arena-level moves enough? (Probably both, with `balance` as the user-facing composition over arena moves.)
11. **RAID5/6.** Are we willing to defer parity RAID to v3+ as Btrfs effectively has? (Recommendation: yes.)
12. **Snapshot deletion cost.** Btrfs's asynchronous `btrfs-cleaner` is a known mount-latency pitfall. NVFS should design the same mechanism but measure its cost explicitly in pre-release load tests.
13. **Scrub scheduling.** User cron vs kernel timer vs arena-embedded schedule hint. Recommendation: arena descriptor carries a "scrub every N days" field; a userspace service runs the actual scrub.
14. **Scrub of uncheckmsummed data.** What to do about `nodatasum` inodes during scrub — skip them silently, report them, or refuse to enable scrub if any exist? Btrfs silently skips; we should probably report.
15. **Mount-time latency ceiling.** Btrfs hit the 10-minute-mount wall before the block-group tree landed. NVFS should commit to a hard upper bound (e.g. 10 s) in design and measure.
16. **Inline extents.** Btrfs stores small files (up to `max_inline`, default ~2 KiB) directly in the fs-tree leaf. This is a metadata-bloat / IOPS-reduction trade-off. Should NVFS support inline extents, given its append-only arena model? (Leaning: yes for META_DURABLE, no for everything else.)
17. **Default csum for each class.** Should NVFS pin the csum algorithm per storage class (META_DURABLE = blake2b-256, DB_WAL = xxhash64, MODEL_IMMUTABLE = blake2b-256, etc.) or globally per filesystem? Per-class is more flexible but harder to reason about during debugging.
18. **Node size.** Btrfs uses 16 KiB nodes; NVFS should probably match. For targets with larger page sizes (ARM64 64 KiB pages, some Simple-OS boards), the node size can scale up to improve branching factor, but on constrained memory devices it can stay at 4 KiB.
19. **Tree forest vs single tree.** Btrfs gains from a forest: independent tree evolution, separate corruption domains, independent scrub. NVFS is currently designed around arena families; the question is whether the arenas-by-class should themselves be B-trees (yes) and whether meta-level indexing needs to cross classes (probably yes; planning needed).
20. **Free-space representation.** Extent list vs bitmap per block group is the Btrfs answer; per-arena free-space in NVFS probably looks different because arenas are append-only. The question is how NVFS's "reclamation" primitive generates free space and whether that generates the same extent-list / bitmap trade-off.

## 18. Top primary sources

**Papers.**

- Ohad Rodeh, "B-trees, Shadowing, and Clones," ACM TOS 3(4), Feb 2008. DOI: 10.1145/1326542.1326544. Preprint PDF: <https://www.usenix.org/legacy/event/lsf07/tech/rodeh.pdf>.
- Ohad Rodeh, Josef Bacik, Chris Mason, "BTRFS: The Linux B-Tree Filesystem," ACM TOS 9(3), article 9, Aug 2013. DOI: 10.1145/2501620.2501623. The canonical description of the shipping design.
- Chris Mason, "Btrfs Design Overview" (talk, FOSDEM 2009 and Linux.conf.au 2012). Slides archived on the LWN and kernel.org wiki.

**Kernel tree.**

- `Documentation/filesystems/btrfs.rst` — the in-tree manual. First source for every feature and every mount option.
- `Documentation/btrfs-send-stream-format.rst` — the send-stream grammar.
- `include/uapi/linux/btrfs_tree.h` — authoritative on-disk structures and item-type constants.
- `include/uapi/linux/btrfs.h` — ioctl interface including `BTRFS_IOC_CLONE_RANGE`, `BTRFS_IOC_FILE_EXTENT_SAME`, `BTRFS_IOC_SEND`, `BTRFS_IOC_RECEIVE`.
- `fs/btrfs/ctree.c`, `disk-io.c`, `transaction.c`, `volumes.c`, `chunk-map.c`, `extent-tree.c`, `relocation.c`, `tree-log.c`, `scrub.c`, `reflink.c`, `compression.c`, `free-space-tree.c`.

**User-space.**

- `btrfs-progs.git`, <https://git.kernel.org/pub/scm/linux/kernel/git/kdave/btrfs-progs.git>.
- `btrfs-progs/Documentation/*.rst` (manpage source).
- The `btrfs(5)` and per-subcommand manpages installed by btrfs-progs.

**Wiki and docs.**

- <https://btrfs.readthedocs.io/en/latest/> — the official documentation migrated from the old kernel.org wiki; kept in sync with the in-tree `Documentation/`.
- <https://btrfs.readthedocs.io/en/latest/Status.html> — feature stability table, particularly the RAID5/6 entry.
- <https://btrfs.readthedocs.io/en/latest/SysadminGuide.html> — operational primer.
- <https://btrfs.readthedocs.io/en/latest/Volume-management.html> — RAID profile semantics.
- <https://btrfs.readthedocs.io/en/latest/Problem-FAQ.html> — the "don't use `--repair`" canon.

**LWN articles (selected, chronological).**

- Corbet, "A short history of btrfs," 2009-07-22, <https://lwn.net/Articles/342892/>.
- Corbet, "Btrfs: working with multiple devices," 2014-01-08, <https://lwn.net/Articles/577961/>.
- "Free space tree," 2015-11-04, <https://lwn.net/Articles/663021/>.
- Corbet, "Status of Btrfs RAID 5/6," 2017-03-01, <https://lwn.net/Articles/720821/>.
- Edge, "Btrfs zstd support," 2017-10-04, <https://lwn.net/Articles/729597/>.
- Bacik talk coverage, LSFMM 2019, <https://lwn.net/Articles/787064/>.
- Corbet, "Btrfs block-group tree," 2022-10-05, <https://lwn.net/Articles/899810/>.
- Coverage of RAID-stripe tree landing, 2023, via the lore.kernel.org linux-btrfs mailing list.

**Mailing list / historical.**

- Chris Mason, original Btrfs announcement, linux-btrfs 12 Jun 2007, <https://lore.kernel.org/linux-btrfs/20070612101134.GA15126@think.oraclecorp.com/>.
- The linux-btrfs mailing list archive (<https://lore.kernel.org/linux-btrfs/>) is the primary source for every feature landed since 2011.

**Industrial.**

- Oracle, "Btrfs File System Administration Guide," <https://docs.oracle.com/en/operating-systems/oracle-linux/8/fsadmin/>.
- Facebook / Meta engineering blog posts on Btrfs at scale (Josef Bacik, Chris Mason; various years).
- SUSE documentation, <https://documentation.suse.com/sles/html/SLES-all/cha-filesystems.html> — the distro-side operational summary.

Where Btrfs documentation is genuinely ambiguous — RAID5/6 write-hole consequence spectrum, exact timing of qgroup rescan, precise conditions under which `nospace_cache` is safe — this report does not pick a single answer. The kernel source and the linux-btrfs mailing list are the only authoritative references for those corner cases, and NVFS design decisions should be grounded in whichever of those artifacts is freshest when the design is finalized.

## 19. Cross-reference index for NVFS design authors

For quick navigation when writing the NVFS design update, this index maps NVFS concerns to the sections above.

- **Superblock design** — §2.1, §10.6 (backup roots), §16.1.
- **B-tree layout** — §2.2, §2.3, §2.4, §16.1.
- **Extent refs** — §2.6, §5.1, §16.1, §16.3.
- **CoW discipline** — §3.1, §3.2, §16.2.
- **Delayed refs** — §3.4, §16.2.
- **Space reservation** — §3.3, §10.5, §16.2.
- **Snapshot semantics** — §4, §16.3.
- **Reflink mechanics** — §5, §16.3.
- **Dedup strategy** — §5.2, §5.5, §16.3.
- **Checksum algorithms** — §6.1, §16.4, Open Q 1.
- **Self-healing** — §6.2, §6.3, §6.6, §16.4.
- **Scrub** — §6.3, §6.6, §16.4, Open Q 13.
- **Compression** — §7, §16.5.
- **Log tree / fsync** — §8, §10.5, §16.7.
- **Send / receive** — §9, §16.6, Open Q 7.
- **Recovery tooling** — §10, §16.7.
- **Quotas** — §11, §16.8, Open Q 6.
- **Allocator** — §12, §16.9.
- **Block groups** — §12.1, §12.4, §16.9.
- **Balance / relocation** — §13, §16.10.
- **Mount options** — §14, §16.11.
- **Zoned / NVMe** — §10.4, §16.12.
- **Performance tradeoffs** — §15.
- **Open questions** — §17.

## 19.1 NVFS storage-class mapping table

The NVFS virtual storage classes map onto Btrfs concepts as follows. This is a design hint, not a specification — the final NVFS design doc is the authoritative reference.

| NVFS class | Btrfs analogue | Recommended profile | Checksum | Compression |
|---|---|---|---|---|
| META_DURABLE | Root tree + extent tree + chunk tree (the "metadata" profile in btrfs terms) | mirror-3 minimum | blake2b-256 | none |
| DB_WAL | Log tree, plus a dedicated subvolume for WAL arenas | mirror-2 minimum | xxhash64 (speed) or blake2b-256 | none |
| DB_TEMP | mixed-bg data | single or mirror-2 | xxhash64 | none |
| MODEL_IMMUTABLE | Read-only snapshot of a data subvolume | mirror-2 or higher | blake2b-256 | zstd level 5+ |
| GENERAL_MUTABLE | Standard data subvolume | single or mirror-2 | blake2b-256 | zstd level 3 (default) |
| CHECKPOINT_SNAPSHOT | Read-only subvolume snapshot | inherited from source | inherited | inherited |

Notes on the mapping:

- META_DURABLE's mirror-3 minimum is a Btrfs best-practice transplant: metadata loss is catastrophic, and paying 3× storage for the small metadata footprint is cheap.
- DB_WAL's xxhash64 choice trades cryptographic strength for latency — WAL writes are in the critical path for every transaction and the WAL is short-lived. A later scrub can verify with a stronger hash if needed.
- DB_TEMP is intentionally not mirrored by default: the data is disposable. The `single` profile saves write bandwidth.
- MODEL_IMMUTABLE compresses aggressively because the data is read many times and written once; the compression cost amortizes.
- CHECKPOINT_SNAPSHOT inherits from source so that a checkpoint does not silently change redundancy or compression state.

### 19.2 The `arena_*` API and Btrfs operations

A rough mapping from Btrfs ioctls to NVFS arena operations (for design reference):

| Btrfs operation | NVFS arena op |
|---|---|
| `BTRFS_IOC_SUBVOL_CREATE` | `arena_create(class, policy)` |
| `BTRFS_IOC_SNAP_CREATE` | `arena_snapshot(source, name, ro)` |
| `BTRFS_IOC_SNAP_DESTROY` | `arena_drop(handle)` |
| `BTRFS_IOC_CLONE_RANGE` / `FICLONERANGE` | `arena_reflink(src_extent, dst_extent, range)` |
| `BTRFS_IOC_FILE_EXTENT_SAME` / `FIDEDUPERANGE` | `arena_dedup_same(a, b, range)` |
| `BTRFS_IOC_SCRUB` | `arena_scrub(handle, policy)` |
| `BTRFS_IOC_BALANCE_V2` | `arena_relocate(handle, filter, convert)` |
| `BTRFS_IOC_SEND` | `arena_send(handle, parent_handle, writer)` |
| `BTRFS_IOC_ADD_DEV` / `RM_DEV` / `DEV_REPLACE` | `arena_device_add/remove/replace(...)` |
| `BTRFS_IOC_DEV_STATS` | `arena_device_stats(devid)` |
| `BTRFS_IOC_GET_SUBVOL_INFO` | `arena_info(handle)` |

The NVFS trait surfaces in `src/lib/nogc_sync_mut/nvfs_if/` should expose an analogue of each of these. The exact API is for the NVFS design doc to specify; this report only asserts that the Btrfs ioctl surface is a complete and battle-tested guide.

## 20. Concluding notes

Btrfs is the most thoroughly documented copy-on-write filesystem in mainline Linux. Its successes (cheap snapshots, integrated checksums, send/receive replication, online device management, compression) are exactly the features NVFS aims to match; its documented failures (RAID5/6 write hole, historical ENOSPC wedges, pre-block-group-tree mount latency, qgroup rescan cost) are exactly the pitfalls NVFS must avoid. Every non-trivial NVFS design decision in the next phase should reference this document alongside the kernel source and the linux-btrfs mailing list. If a claim in this document disagrees with either authoritative source, the kernel source wins; this is a research synthesis and not a spec.

Three specific Btrfs features were **not** deeply explored here because they are either out-of-scope or insufficiently documented in primary sources for responsible summarization:

- **Encryption.** Btrfs reserves a byte in EXTENT_DATA for an encryption flag; no algorithm is implemented in mainline. Proposals to ship fscrypt-style per-inode encryption are perennial on the list but have not merged. NVFS encryption design should draw from fscrypt and dm-crypt, not from Btrfs.
- **Raid-stripe tree internals.** The `RAID_STRIPE_TREE` incompat feature is new and under active development; the on-disk format is documented only in the patch series and will change before stabilization. NVFS should track this and adopt a stabilized version, not a preview.
- **Sub-page I/O.** Running Btrfs with `sectorsize < pagesize` (e.g. 4 KiB sectors on ARM64's 64 KiB page) is supported since 5.15 but has a long tail of edge cases in the kernel source. NVFS should pin the sector size to match its page size to avoid this complexity.

Writing for an NVFS port means knowing what to leave out as much as what to take in. Btrfs is a big codebase (~180 kloc in `fs/btrfs/` as of kernel 6.11) and not all of it is worth porting. The translation table in §16 is the answer to "what is worth it" — everything marked KEEP or ADAPT. Everything marked SKIP is something NVFS gets to skip in v1 and revisit only if evidence demands it.

This document is intentionally structured so that a later Codex or reviewer pass can diff-merge in clarifications, corrections, or expansions without re-authoring. Section numbers are stable; adding subsections within a section is preferred over renumbering.
