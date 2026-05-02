# ZFS Deep Dive — Feature Catalogue for NVFS Port

**Status:** Phase 1 research deliverable (2026-04-17).
**Companion docs:** `doc/01_research/spostgre_research.md`, `doc/05_design/nvfs_design.md`.
**Scope:** Research only. No design doc. No code. Feature-by-feature catalogue of ZFS, with a KEEP / ADAPT / SKIP / ATTACH verdict for NVFS at the end of each section and a consolidated translation table in §16.

This document is intentionally dense on primary-source citations because the ZFS literature has drifted; reproducing anything from a blog-of-a-blog is a known trap. When an empirical claim is ambiguous across sources (e.g. DDT RAM sizing, silent-corruption rates), the ambiguity is flagged inline with the word **[AMBIG]** rather than smoothed over.

## 1. Executive summary

ZFS is simultaneously a volume manager, a RAID stack, a filesystem, a snapshot/replication engine, a compression/dedup/encryption layer, and an in-band data-integrity auditor. Its defining design choices are: (a) **copy-on-write (CoW) everywhere**, (b) **Merkle-tree-wide checksums** stored in the parent block pointer rather than alongside the data, (c) **transaction groups (txg)** that commit all pool state atomically, (d) **pooled storage** with dynamically striped top-level vdevs, and (e) **self-healing reads** that compare checksum and fall over to a redundant copy or parity reconstruction transparently. These properties together produce the end-to-end integrity guarantee that other filesystems synthesize only partially (dm-integrity+md+xfs+LUKS is a common rough equivalent on Linux, with more moving parts).

The design is documented primarily in:

1. **Jeff Bonwick and Matt Ahrens, "ZFS: The Last Word in Filesystems,"** Sun Microsystems internal/LISA '07 material, later presented and mirrored as the OpenSolaris ZFS On-Disk Specification (also known as the "ZFS On-Disk Format" paper, Sun 2006). This is the original on-disk spec; all later ZFS forks trace their uberblock, blkptr, DMU, and SPA layouts to this document.
2. **OpenZFS documentation**, hosted at https://openzfs.github.io/openzfs-docs/ (project documentation), https://openzfs.github.io/openzfs-docs/Performance%20and%20Tuning/Workload%20Tuning.html, and the OpenZFS Wiki at https://openzfs.org/wiki/Main_Page.
3. **illumos manual pages** — `zpool(8)`, `zfs(8)`, `zdb(8)`, `zpool-events(8)`, `zpoolprops(7)`, `zfsprops(7)` — which remain the canonical reference for command semantics.
4. **FreeBSD Handbook, Chapter 22 "The Z File System (ZFS)",** https://docs.freebsd.org/en/books/handbook/zfs/.
5. **Dominic Giampaolo, "Practical File System Design with the Be File System"** (Morgan Kaufmann 1999) — pre-ZFS but still the clearest textbook on 64-bit extent-based metadata, journaling, and attribute stores, and often cited as prior art for ZFS's DMU.
6. **OpenZFS Developer Summit (OZDS) proceedings**, 2013–2024, specifically the dRAID talks (OZDS 2019, 2020), the persistent L2ARC talks (OZDS 2019), the fast-dedup proposal (OZDS 2023), and the encryption talks (OZDS 2016–2017).
7. **Bonwick, "RAID-Z,"** blog post 2005 (archived at https://blogs.oracle.com/bonwick/raid_z and mirrored widely); **Bonwick, "ZFS End-to-End Data Integrity,"** blog post 2005 (archived at https://blogs.oracle.com/bonwick/zfs-end-to-end-data-integrity).
8. **Bairavasundaram et al., "An Analysis of Data Corruption in the Storage Stack,"** FAST '08 (NetApp + UW-Madison) — the 1.5 M disk / 41 month silent-corruption survey that ZFS partisans cite; and **Panzer-Steindel, "Data Integrity,"** CERN Internal Report, 2007 (the 33 TB test that found ~152 corrupt files at the OS/disk layer over three weeks).
9. **OpenZFS source tree**, https://github.com/openzfs/zfs, specifically `module/zfs/spa.c`, `module/zfs/dmu.c`, `module/zfs/zil.c`, `module/zfs/arc.c`, `module/zfs/vdev_raidz.c`, `module/zfs/vdev_draid.c`, `module/zfs/ddt.c`, `module/zfs/zio_crypt.c`, `include/sys/spa.h`, `include/sys/dmu.h`, `include/sys/zio.h`, `include/sys/blkptr.h`, `include/sys/uberblock_impl.h`, `include/sys/vdev_impl.h`.

NVFS is a user-space, arena-oriented filesystem targeting NVMe/ZNS/FDP SSDs under Simple's MDSOC+ECS stack; many ZFS ideas map directly (Merkle integrity, CoW, send/receive, ARC-style cache, snapshots), some map with adaptation (RAID-Z stripe-width, metaslabs → arenas), and some should be skipped or replaced (in-kernel locking, ARC-vs-pagecache arbitration, in-line dedup as default). §16 gives the consolidated verdict.

## 2. On-disk architecture

### 2.1 Layered view: SPA / DMU / ZPL / ZIL

ZFS separates concerns into four stacked subsystems, with well-defined interfaces between each. Bonwick and Ahrens (2006 on-disk format) present these as three layers (SPA, DMU, ZPL), with ZIL threaded through the DMU; the OpenZFS source tree follows the same decomposition.

- **Storage Pool Allocator (SPA)** — the lowest layer. Manages vdevs, metaslabs, the allocator, I/O pipeline (`zio`), checksum computation, compression, encryption, and the uberblock. Exposes block-allocate / block-free / read / write APIs keyed by `blkptr_t`. Source of truth: `module/zfs/spa.c`, `module/zfs/metaslab.c`, `module/zfs/zio.c`, `module/zfs/vdev.c`, `include/sys/spa.h`, `include/sys/spa_impl.h`.
- **Data Management Unit (DMU)** — the transactional object store. Turns the SPA's block-level interface into "objects" (64-bit object IDs) and "object sets" (collections of objects). Objects are typed (`dnode_phys_t` fields include `dn_type`, e.g. `DMU_OT_PLAIN_FILE_CONTENTS`, `DMU_OT_DIRECTORY_CONTENTS`, `DMU_OT_ZAP_OTHER`, `DMU_OT_INTENT_LOG`, `DMU_OT_DSL_DATASET`, etc.). Transactions are created by `dmu_tx_create`, assigned to a txg, and committed by `dmu_tx_commit`. Source of truth: `module/zfs/dmu.c`, `module/zfs/dnode.c`, `module/zfs/dbuf.c`, `include/sys/dmu.h`, `include/sys/dnode.h`.
- **ZFS POSIX Layer (ZPL)** — the POSIX filesystem view: directories, files, xattrs, ACLs. Maps VFS operations onto DMU objects. Source of truth: `module/zfs/zfs_vnops.c`, `module/zfs/zfs_vfsops.c`, `module/zfs/zfs_dir.c`, `include/sys/zfs_vfsops.h`.
- **ZFS Volume Layer (ZVOL)** — parallel to ZPL, exposes a DMU object set as a raw block device.
- **ZFS Intent Log (ZIL)** — per-dataset synchronous-write fast path. Appends intent records; replayed on import after a crash. Source of truth: `module/zfs/zil.c`, `include/sys/zil.h`, `include/sys/zil_impl.h`. Discussed in detail in §9.

The interface across layers is narrow enough that the DMU is in principle reusable. The lumofs / ZFS-on-OSD research (OZDS talks, 2015–2017) and Oracle's internal rumors about a DMU-backed object store all assume this separation.

### 2.2 vdev topology

A ZFS **pool** is a tree of `vdev_t` nodes:

- The root vdev has N **top-level vdevs** as children. Data is **dynamically striped** across top-level vdevs at allocation time: the SPA allocator picks a top-level vdev based on free space, ashift compatibility, and allocation-class rules (§12).
- Each top-level vdev is one of:
  - **leaf (disk/file)** — a single physical disk, file, or partition
  - **mirror** — N-way mirror of leaf vdevs
  - **raidz1 / raidz2 / raidz3** — single/double/triple-parity RAID-Z (§3)
  - **draid1 / draid2 / draid3** — distributed RAID (§3.3)
- Top-level vdevs may not be nested arbitrarily; only (mirror | raidz* | draid*) of (leaf), i.e. two levels. (This is a long-standing ZFS limitation; you cannot do RAID-Z on top of mirrors in one pool, only by stacking pools.)
- Special vdev classes, attached at the top level, serve specific allocation classes (§12):
  - **log** (SLOG) — holds the ZIL for synchronous writes; must be mirrored for durability
  - **cache** — L2ARC (§10)
  - **special** — metadata + small-blocks allocation class
  - **dedup** — DDT allocation class
  - **spare** — hot spare, no data until autoreplace

Primary reference: `zpoolconcepts(7)` illumos man page, and `include/sys/vdev_impl.h` (`vdev_t`, `vdev_ops_t`).

### 2.3 Labels (L0–L3)

Each leaf vdev stores **four labels**: L0 and L1 at the start of the device, L2 and L3 at the end. Each label is 256 KiB and contains an XDR-encoded name-value list describing the pool config (GUIDs, pool name, vdev tree, txg), followed by a 128-KiB **uberblock array** (128 slots of 1 KiB each, historically; some variants differ by ashift).

The four labels exist to survive partial device-front or device-end damage. When importing, ZFS reads all four, picks the one with the highest txg, and cross-validates. The write protocol writes labels in two phases (L0/L2 first, then L1/L3) so that a crash between phases still leaves a consistent pair readable. Primary reference: `module/zfs/vdev_label.c`, section "The Label" of the Bonwick/Ahrens on-disk format document.

Label internal structure (from the on-disk format document, §1.3):

- 8 KiB **blank space** at the very start (for boot headers / MBRs on boot-disks).
- 8 KiB **boot header** — currently unused, reserved.
- 112 KiB **name/value pair list** (XDR-encoded nvlist). Fields include `version` (spa version), `name` (pool name), `state` (active/exported), `txg`, `pool_guid` (64-bit unique pool GUID), `top_guid` (top-level vdev GUID this label belongs to), `guid` (leaf vdev GUID), `vdev_tree` (a recursively-nested nvlist of the entire pool vdev topology), `features_for_read`, `hostid`, `hostname`.
- 128 KiB **uberblock array** — 128 × 1 KiB uberblock slots (may be 32 × 8 KiB on ashift≥13 vdevs, since each uberblock must be a single sector-write atomic).

The four-label layout handles four classes of failure: front-of-disk corruption (partition-table accident), end-of-disk corruption (device truncation), single-sector errors (labels are redundant within the 256 KiB region), and off-by-vdev-guid-sum (sanity check during import). The L2/L3 end-of-device labels matter in particular because an accidental `dd if=/dev/zero of=/dev/sdX count=1M` only wipes the start of the device; the trailing labels still identify the pool and allow recovery via `zpool import -d`.

### 2.4 Uberblock array + rotation

The uberblock is the root of the entire pool Merkle tree. It contains:

- `ub_magic` (0x00bab10c, "ooh-baby-look")
- `ub_version` — on-disk version (legacy) or feature-set references
- `ub_txg` — the txg this uberblock committed
- `ub_guid_sum` — sum of all vdev GUIDs at commit time (sanity check for missing vdevs)
- `ub_timestamp`
- `ub_rootbp` — the **blkptr** pointing at the MOS (Meta-Object Set, object ID 1 within the pool), which is the root of all pool metadata

Each txg, the syncing thread writes a new uberblock into slot `txg % ub_slots` of the uberblock array in each label. After writing all data blocks and flushing caches, it picks the uberblock slot to commit. Import chooses the uberblock with the highest `ub_txg` that passes checksum. A corrupted latest uberblock simply causes fallback to the previous one (`zpool import -T txg` lets the admin select manually; `zpool import -F` rewinds).

Primary reference: `include/sys/uberblock_impl.h`, `module/zfs/uberblock.c`, `module/zfs/spa.c` (`spa_load_impl`, `spa_ld_select_uberblock`).

Uberblock commit ordering (from `spa_sync` and the `module/zfs/vdev_label.c` `vdev_uberblock_sync` / `vdev_uberblock_sync_done` path) proceeds in strict dependency order:

1. Write every dirty indirect block at every level, bottom-up, so that when a parent's checksum is recomputed, its child has already committed.
2. Write the MOS root indirect.
3. Issue `zio_flush` to every leaf to force power-loss-safe media commit — this is critical on devices with volatile write caches; without it, the uberblock write can reach the platter before the data blocks.
4. Write the uberblock into `txg % N` slot. The uberblock write itself is **aligned to a single sector** so that a torn write either writes the entire new uberblock or leaves the previous one in place. This atomicity is what allows the pool to survive crashes across an uberblock update without any additional journaling.
5. Issue a final `zio_flush`.
6. The pool now considers the txg synced; in-memory structures release the old blkptrs.

Missing or delayed flush commands between step 2 and step 4 are the single most common cause of post-crash pool inconsistency on commodity SATA that silently ignores `FLUSH_CACHE`; OpenZFS issues per-vdev flush unconditionally, and the NVMe driver honors it via `nvme_flush`.

### 2.5 Transaction groups (txg)

A **txg** is a monotonically increasing 64-bit integer identifying an atomic commit of pool state. At any moment, three txg states coexist:

1. **open** — the active txg, accepting new DMU transactions. `dmu_tx_assign()` places new work here.
2. **quiescing** — the transitional state. No new transactions are assigned; outstanding ones drain to completion.
3. **syncing** — the syncing thread (`spa_sync`) walks the dirty object list, writes out all CoW blocks in dependency order, writes the uberblock, and flushes caches.

The three-phase pipeline means at any moment, up to three txgs (N, N-1, N-2) are live in different phases, giving write-coalescing and parallelism. Default txg commit interval is 5 seconds (`zfs_txg_timeout`), tunable from 1 to 30 seconds.

Primary reference: `module/zfs/txg.c`, `include/sys/txg.h`, `include/sys/txg_impl.h`; Bonwick, "Smokin' Mirrors," blog post 2006 (on why SSDs make txg coalescing cheaper).

Pressure tuning: when the dirty-data set exceeds `zfs_dirty_data_max` (default min(10% of RAM, 4 GiB)), the `dmu_tx_delay` mechanism slows incoming transactions by injecting calibrated microsecond delays so that the syncing thread can catch up. The delay scales quadratically with overage, so a mild overshoot is transparent and a severe one throttles aggressively. This is ZFS's answer to the classic "write storm then fsync stall" pattern in buffered filesystems — it deliberately smooths the write curve rather than accepting large-amplitude backpressure.

Open txg state machine transitions (`txg_thread_enter`, `txg_sync_thread`, `txg_quiesce_thread`):

- `txg_open` (state 0) — txg N is open; assigns accept it. Transition to quiescing is triggered either by `zfs_txg_timeout` elapsing or by `zfs_dirty_data_sync_percent` of `zfs_dirty_data_max` being dirty.
- `txg_quiescing` (state 1) — outstanding assigns drain. No new assigns.
- `txg_syncing` (state 2) — dirty-data writeout. The pipeline drives writes through zio stages.
- `txg_synced` — all I/O complete, uberblock committed. The in-memory data release happens here.

At any given wall-clock moment the pool typically has txg N open, N-1 quiescing or syncing, and N-2 synced but not yet garbage-collected. The overlap is where ZFS gets its ability to sustain high write throughput despite the nominal 5-second txg commit cadence.

### 2.6 Block pointers (blkptr_t)

The `blkptr_t` is the structural unit that chains the Merkle tree. Its definition lives in `include/sys/blkptr.h` (older: `spa.h`). A **fat** blkptr is 128 bytes (three DVA slots, plus full metadata); a **skinny** / embedded blkptr (EMBEDDED_BP) is 112 bytes and carries up to 112 bytes of data inline instead of a DVA (used for tiny objects and gang headers). Fields of a fat blkptr:

- **DVA[0..2]** — up to three Data Virtual Addresses. A DVA is `(vdev_id, offset)`, 16 bytes, pointing at the physical location. Multiple DVAs implement **ditto blocks**: the SPA stores up to three copies of a block, on distinct vdevs if possible, typically for metadata (the more critical the block, the more ditto copies — uberblock MOS indirects get 3 copies).
- **`lsize`** — logical size (before compression)
- **`psize`** — physical size (after compression)
- **`compress`** — compression algorithm ID
- **`checksum`** — checksum algorithm ID
- **`type`** — DMU object type
- **`level`** — indirection level (0 = leaf, n = n-th indirect)
- **`birth txg`** — the txg in which this blkptr was born; used for incremental send, snapshot dead-lists, and scrub pruning
- **`fill count`** — total number of non-hole blkptrs in the subtree rooted here (enables O(1) answer to "is any data here?")
- **`checksum[0..3]`** — 256-bit (four 64-bit words) checksum of the **logical** (decompressed, decrypted) child data. Stored in the parent, not with the child — this is what makes the Merkle property work.

Primary reference: `include/sys/spa.h` (the `blkptr_t` union + macros is the canonical layout), `include/sys/blkptr.h`, Bonwick/Ahrens on-disk format §3.

Embedded blkptrs (BP_EMBEDDED) deserve special mention: when a block's compressed size is ≤ 112 bytes, the data can be stored **inline** in the blkptr itself, skipping allocation entirely. Zero blocks and tiny xattr values are the common case. The embedded-blkptr path sets the `BP_EMBEDDED` flag, re-purposes the DVA fields as data bytes, and stores the algorithm used. This is a significant space and I/O savings for sparse files and metadata, and a neat example of the CoW pointer structure doubling as a micro-allocation mechanism.

Gang blocks are the opposite extreme: when the allocator cannot find a contiguous region large enough for a logical block, it emits a **gang header** — a small on-disk structure containing up to three sub-blkptrs pointing at fragments — and sets the `G` (gang) bit on the parent blkptr. Gang blocks are the last-resort mechanism; high gang-block rate indicates severe fragmentation and is visible in `zdb -bbbb`.

The birth-txg field is actually **two fields** in modern OpenZFS blkptrs: `blk_phys_birth` (the txg in which the physical block was allocated) and `blk_logical_birth` (the txg in which the logical entity was created). For most blocks they are equal. They diverge when a block is rewritten in-place-of-a-freed-position (rare) or when a redacted dataset is reconstructed. Incremental send and scrub use `blk_phys_birth`; dataset semantics use `blk_logical_birth`. This split was added to support redacted / rewritten-block send streams without breaking the birth-based pruning optimization.

### 2.7 Indirect blocks

Object bodies larger than a single data block are addressed by a tree of indirect blocks: a dnode has up to `BPS_PER_DNODE` (3 by default) directly-reachable blkptrs; beyond that, indirect blocks (full 128-KiB-ish blocks of blkptrs) extend the tree to depth up to 6 levels. This covers up to `recordsize × fanout^6` ≈ multi-exabyte objects.

Indirect-block width is determined by `indirect_block_shift` (default 14 → 16 KiB indirect blocks before the 2019 change; the modern default depends on the `recordsize`). `zdb -ddd` inspects indirect structures.

Primary reference: `module/zfs/dnode.c`, `module/zfs/dbuf.c`, `include/sys/dnode.h`.

### 2.8 Checksum algorithms

Each blkptr's checksum algorithm is selected at allocation time and recorded in the blkptr. Available algorithms (from `include/sys/zio.h` enum `zio_checksum`):

- **fletcher2** (legacy, deprecated for data, still used for ZIL where speed matters more than strength)
- **fletcher4** — 4-word Fletcher checksum, fast, weak cryptographically but adequate for accidental corruption. **Default** for user data.
- **sha256** — cryptographically strong; required for dedup (dedup=on implies sha256)
- **sha512-256** — SHA-512 truncated to 256 bits; ~50% faster than sha256 on 64-bit CPUs (Intel/AMD)
- **edonr** — Edon-R, variable-length
- **skein** — Skein hash function
- **blake3** — BLAKE3, added in OpenZFS 2.2 (2023); strong and extremely fast on modern CPUs via SIMD; reasonable modern default if platform support exists

Dedup requires a **cryptographic** checksum (sha256 / sha512-256 / edonr / skein / blake3) because collision-on-fletcher4 would cause silent data corruption on dedup matches.

Primary reference: `module/zfs/zio_checksum.c`, `module/zfs/sha2/`, `module/zfs/blake3/`.

Performance note (from the OpenZFS blake3 merge discussion, 2023): on modern x86_64 with AVX2/AVX-512, **blake3** reaches ~6 GB/s/core, roughly 3–5× faster than sha256 and competitive with hardware-accelerated AES-NI paths. On ARMv8 with crypto extensions, sha256 benefits from SHA-NI acceleration and is competitive with blake3. On RISC-V without vector extensions, fletcher4 (non-cryptographic, SIMD-friendly) remains the only practical option. Algorithm choice is therefore a platform-dependent CPU-budget decision, not a one-size-fits-all default.

Checksum verify happens on every read (`zio_checksum_verify` stage in the zio pipeline). Failure increments the per-vdev `checksum_errors` counter, triggers self-healing (§5.2) if a redundant copy is available, and raises a `ereport.fs.zfs.checksum` ereport consumed by `zed` to notify the admin.

Salted checksums: ZFS includes a per-pool random salt that is mixed into the checksum for specific block types (e.g. `SPA_FEATURE_SHA512`). This prevents known-plaintext pre-image attacks against pool checksums but does not authenticate — for authenticated integrity, use native encryption (§13), which adds a keyed MAC.

**NVFS verdict (§2):** KEEP the SPA/DMU/ZPL/ZIL layering (it maps cleanly onto MDSOC-outer axes), KEEP blkptr-style Merkle parent-stores-child-checksum, KEEP uberblock rotation (it is exactly the "atomic publish pmap root" pattern already in the NVFS design), KEEP txg three-phase pipeline (adapt as "arena seal + publish pmap root"), ADAPT vdev topology (NVFS pools are user-space and arena-local; mirrors and parity are capability-probed, not universal), ATTACH multi-label for devices where we can reach the LBA tail, SKIP ZVOL for M1 (no block-device exposition), KEEP fletcher4 + blake3 as the initial checksum set.

### 2.9 ZPL — POSIX layer details

The ZPL (`module/zfs/zfs_vnops.c`, `zfs_dir.c`, `zfs_znode.c`) maps POSIX onto DMU objects. Key mappings:

- Each file / directory / symlink is a DMU object of type `DMU_OT_PLAIN_FILE_CONTENTS`, `DMU_OT_DIRECTORY_CONTENTS`, or `DMU_OT_SYMLINK`. Metadata (mode, uid, gid, times) is stored in the `SA` (System Attributes) layout, which is itself a DMU object referenced by the file's dnode.
- Directories are **ZAP** (ZFS Attribute Processor) objects — extendible hash tables keyed by name, values are `(object-id, object-type)`. Large directories use `fzap` (fat ZAP); small ones use `microzap` (a flat list). Automatic promotion from microzap to fzap happens at a threshold directory size.
- Hard links share a dnode; reference-counted via `zfs_znode_t` and the `ZFS_LINK_OBJ` attribute.
- Symlinks ≤ ~120 bytes are stored inline in the dnode's SA block (no data block allocated); longer symlinks get a normal file body.

**xattrs** are stored in one of two layouts selectable per-dataset:

- `xattr=dir` (legacy) — each xattr becomes a hidden file in a hidden directory attached to the host file. Readable/writable via standard file APIs internally. Portable but slow (every xattr access is a directory lookup + file read).
- `xattr=sa` (default since OpenZFS 0.6+) — xattrs are stored inline in the dnode's SA block, reading with the host file's dnode. Fast but has a size limit (~100 bytes per xattr; larger ones spill to a separate DMU object).

**ACLs** follow NFSv4 ACL semantics (`aclmode`, `aclinherit` properties), richer than POSIX permissions. ZFS stores ACLs in the SA block when `acltype=nfsv4`; `acltype=posixacl` gives Linux POSIX ACLs stored as xattrs.

Primary reference: `module/zfs/zfs_acl.c`, `module/zfs/sa.c`, `include/sys/sa_impl.h`.

### 2.10 Properties — the unified knob surface

Every dataset has properties in three classes (`module/zfs/zfs_ioctl.c`, `zfsprops(7)`):

- **Native** — built-in properties: `recordsize`, `compression`, `checksum`, `dedup`, `encryption`, `atime`, `relatime`, `xattr`, `acltype`, `canmount`, `mountpoint`, `sync`, `primarycache`, `secondarycache`, `quota`, `refquota`, `reservation`, `refreservation`, `casesensitivity`, `normalization`, `utf8only`, `readonly`, `devices`, `exec`, `setuid`, `logbias`.
- **User** — custom properties prefixed with `user:` or with a `:`-separated module namespace, e.g. `com.example:backup-policy=weekly`.
- **Inherited** — child datasets inherit from parent by default; `zfs inherit -r` forces re-inheritance.

Properties are a persistent configuration surface, set/got via `zfs set` / `zfs get`, and serialized in send streams (preservable across replication). Value semantics include `on|off`, `default`, `local`, `inherited from <dataset>`, and `-` (not set).

Three property semantics deserve specific note:

- `recordsize` — the logical block size. Default 128 KiB. Applies to newly-written blocks only; changing it does not rewrite existing data. For databases with 8 KiB / 16 KiB pages, setting `recordsize` to match prevents read-modify-write amplification.
- `ashift` — vdev-level, not dataset-level, set at pool creation. The invariant: `recordsize >= 2^ashift`, else the minimum allocation unit exceeds the logical block size.
- `canmount=off` — the dataset has all other properties (inheritance parent, quota, etc.) but cannot be mounted. Useful for creating "container datasets" that group children without being directly mountable.
- `logbias={latency|throughput}` — influences ZIL placement. `latency` (default) uses the SLOG aggressively for low-latency sync. `throughput` bypasses the SLOG and writes sync data to the main pool, optimizing for bulk-sync workloads where sync-commit frequency is low.
- `quota` vs `refquota` — `quota` counts all space used by the dataset and descendants (snapshots, clones); `refquota` counts only space uniquely referenced. The distinction matters because snapshots count toward `quota` but not `refquota`, which changes the user-visible meaning under heavy snapshot usage.
- `reservation` vs `refreservation` — reserved-space analog of the quota distinction. `reservation` reserves space for dataset + descendants; `refreservation` reserves only for unique references. The PostgreSQL-on-ZFS best practice is `refreservation` equal to dataset size to guarantee no write fails due to pool exhaustion regardless of snapshot activity.
- `atime=off` + `relatime=on` — the combination that most operators end up at: disable full atime updates (huge write amplification) but allow relatime-style updates for compatibility with tools that key off access time.
- `casesensitivity={sensitive|insensitive|mixed}` — set at dataset creation, immutable after. Default is `sensitive`. `insensitive` is required for SMB compatibility. `mixed` lets the application choose per-lookup via a special flag (Samba uses it).
- `utf8only={on|off}` and `normalization={none|formC|formD|formKC|formKD}` — Unicode normalization of filenames. `utf8only=on` rejects non-UTF-8 names; `normalization=formD` normalizes all names to NFD (useful for HFS+ interop). Changing these properties after dataset creation is not allowed.
- `snapdir={hidden|visible}` — whether `.zfs/snapshot/` is a visible directory in the dataset mount. Default hidden; many admins set it visible for easier snapshot browsing.

## 3. Copy-on-write and transactional semantics

### 3.1 The never-overwrite rule

Bonwick's central claim (2005 blog, 2006 on-disk paper): **every write allocates a new block**. The old block is not freed until all surviving references (snapshots, clones, the txg-before-last) have released it. This is the property that makes ZFS:

- Crash-consistent without a separate journal (the uberblock is the commit, and it either points at a fully-linked new tree or a fully-linked old tree)
- Able to offer O(1) snapshots (a snapshot is just a pinned blkptr tree)
- Able to detect torn writes (new blocks land at new addresses; a torn write corrupts only the new block, whose checksum will flag it)

Mechanism: the SPA allocator picks a free metaslab range, writes the new data, recomputes checksums up the parent chain, and eventually rewrites the uberblock slot. The old path is structurally unreachable after the new uberblock is committed.

### 3.2 txg commit pipeline (detail)

Covered structurally in §2.5. In detail (`spa_sync` in `module/zfs/spa.c`):

1. **Quiesce**: stop accepting new `dmu_tx_assign` for the txg-being-closed; wait for outstanding ones to call `dmu_tx_commit`.
2. **Sync pass**: walk dirty dbufs in DMU object dependency order. For each, allocate new block(s) via `zio_alloc`, compute compressed output, compute checksum, issue `zio_write`. The zio pipeline (`zio_stage` state machine in `module/zfs/zio.c`) handles compression → encryption → checksum → allocation → I/O in a fixed stage order.
3. **Pool-level metadata sync**: MOS, space maps (§12), deadlists, DDT (if dedup), ZIL headers.
4. **Multiple sync passes**: freeing blocks can dirty new blocks (space-map updates); the syncing code iterates until the dirty list is empty. There is a cap (`zfs_sync_pass_deferred_free`, default 2) on how many passes allocate new blocks versus deferring frees to the next txg.
5. **Write uberblock**: when the dirty list is clean, write the new uberblock into `txg % 128` slot of each label on each leaf vdev.
6. **Flush caches**: issue `zio_flush` to each vdev to force the physical cache to media. Then the txg is **synced**.

The Merkle-tree-over-blkptr structure means any crash before step 5 leaves the previous uberblock as the live root; the in-flight new tree is orphaned and will be freed on the next allocation walk. A crash between step 5 and step 6 can leave the uberblock-on-disk advertising blocks that have not reached the platter — this is why the per-vdev cache flush is mandatory. (The same trap bit NTFS and ext4 if barriers are disabled.)

### 3.3 Merkle-tree integrity

Every non-embedded blkptr carries a 256-bit checksum of the **logical** child block. The child's checksum is not stored on the child itself; the child's integrity is verified only by following the parent pointer. Consequences:

- A silently-corrupted block is detected on read: the parent-held checksum won't match the recomputed checksum of the child's content.
- You cannot forge a block without forging the parent chain up to an uberblock. Cryptographically strong checksums (sha512-256, blake3, skein) plus optional encryption (§13) push this from "you can't by accident" to "you can't on purpose."
- The uberblock itself has a self-checksum (SHA-256 over the uberblock), since there is no parent. This is the single point where the Merkle property terminates.
- Scrubs (§4.3) revalidate the whole tree by walking blkptrs and reading each referenced block.

**NVFS verdict (§3):** KEEP CoW and txg-three-phase; NVFS's "arena seal + pmap-root publish" is the same pattern phrased differently. KEEP Merkle parent-stores-child-checksum; it is what makes out-of-place durable commits rigorous. ADAPT: NVFS's pmap root is per-pool equivalent of the MOS root blkptr; uberblock rotation is already planned.

## 4. RAID-Z, mirrors, and dRAID

### 4.1 RAID-Z (Z1 / Z2 / Z3)

RAID-Z is ZFS's answer to the RAID-5/6 write-hole. Primary reference: Bonwick, "RAID-Z" blog 2005; `module/zfs/vdev_raidz.c` and the RAID-Z math paper mirrored from Plank (referenced by the source comments).

The three critical differences from traditional RAID-5:

1. **Variable-width stripes**. A write of size `N * sector` + parity lays out exactly `N + P` sectors. There is no fixed stripe width. The blkptr records the stripe size so reads reconstruct correctly.
2. **No read-modify-write**. Every write is a full-stripe write. Combined with CoW (so there is never a partial overwrite), the RAID-5 write-hole disappears: you never have the situation where a partial-stripe write has updated data but not parity (or vice versa) across a power failure.
3. **Parity is filesystem-aware**. The filesystem knows exactly which sectors belong to which stripe, so a missing-disk rebuild only rewrites **allocated** blocks, not the whole disk. Resilver time scales with used capacity, not device capacity (§4.5).

Galois-field parity math: RAID-Z1 is single-parity (XOR); Z2 adds Reed-Solomon Q parity (mul by α in GF(2^8)); Z3 adds R parity (mul by α² in GF(2^8)). The algorithms are documented in Plank, "A Tutorial on Reed-Solomon Coding for Fault-Tolerance in RAID-like Systems" (1997) and verified in the ZFS source comments.

**RAID-Z Trade-offs** (from OpenZFS docs "RAID-Z" and Performance Tuning pages):

- RAID-Z *read* IOPS is approximately that of a single disk per vdev, because each logical block is spread across all disks of the vdev — an entire block must be read and checksummed before ZFS can return data.
- RAID-Z *streaming* throughput scales with disk count minus parity.
- The "ashift tax": RAID-Z on 4-KiB-sector disks (ashift=12) incurs parity-padding overhead that makes small recordsizes grossly space-inefficient. The OpenZFS matthewahrens "ashift" discussions and the Delphix padding calculators (2017) document this in detail.

### 4.2 Mirrors

Mirror vdevs are N-way mirrors of leaf vdevs. Reads pick one leaf per logical I/O, using a latency-weighted scheme (`vdev_mirror_io_start` in `module/zfs/vdev_mirror.c`) that biases toward the fastest-responding leaf. Writes go to all leaves in parallel; completion is when all acknowledge.

On checksum mismatch, ZFS reads from a sibling mirror, verifies, and **writes the good data back** to the failing leaf (this is self-healing, §5.2). If all mirrors fail checksum, the read returns `EIO`.

Mirrors outperform RAID-Z on random workloads (per-leaf IOPS is additive on read, not divided), which is why high-IOPS ZFS setups use mirror-vdev pools (often called "stripe of mirrors," or "RAID-10 ZFS-style").

### 4.3 dRAID

**dRAID** (distributed RAID) was introduced in OpenZFS 2.1 (2021); see OZDS 2018 and OZDS 2019 talks by Mark Maybee. Primary reference: `module/zfs/vdev_draid.c`; `zpoolconcepts(7)` `draid` paragraph.

dRAID solves two RAID-Z weaknesses:

1. **Fixed stripe width**. Unlike RAID-Z's variable-width stripe (one block per stripe), dRAID uses a fixed-width stripe (like traditional RAID-5/6), so the space-efficiency math is predictable, especially for small blocks where RAID-Z suffers.
2. **Distributed hot spares**. A hot-spare's capacity is pre-allocated as spare sectors across all disks in the vdev; a failed-disk rebuild writes reconstructed data into the distributed spare in parallel across all surviving disks, multiplying rebuild throughput.

dRAID is configured as `draid1`, `draid2`, `draid3` (parity level) with parameters `data=`, `children=`, `spares=`. For example, `draid2:8d:11c:1s` means 2 parity, 8 data drives per stripe, 11 children total, 1 distributed spare.

The trade-off: dRAID's fixed stripe width means small-block writes have parity overhead similar to traditional RAID-5/6, which for metadata-heavy workloads is worse than RAID-Z's variable-width approach. dRAID pools typically use a **special vdev** (§12) to offload small blocks and metadata, reclaiming RAID-Z's small-block efficiency.

### 4.4 Why ZFS avoids the RAID-5 write-hole

The RAID-5 write-hole is the scenario where, during a partial-stripe write, a power failure causes the data sectors to update but the parity sector to remain stale (or vice-versa). On subsequent disk failure, reconstructed data from stale parity is silently wrong. Mitigations (battery-backed RAID controllers, ZFS's RAID-Z) take different approaches:

- **Battery-backed cache** keeps the write in-flight through a reboot and replays it.
- **RAID-Z** makes the update unit atomic: CoW means no in-place update, and the whole new stripe (data + parity) lands at a fresh location; the uberblock atomically flips the reference.

This is covered by Bonwick, "RAID-Z" blog and the OpenZFS "RAID-Z Compared To RAID-5" docs page.

### 4.4.1 Torn-write resistance in detail

The CoW write path's torn-write story has three layers:

1. **Data block**: a new data block is written to a freshly allocated DVA. A torn write at this layer corrupts only the new copy; the old copy (still referenced by the still-live parent) remains intact until its own parent is rewritten. Checksum verification on read would catch the torn new block before it is reached.
2. **Indirect blocks**: same as data blocks — CoW means new indirects are written to fresh DVAs.
3. **Uberblock**: a single sector write. Sector-write atomicity is a device-level guarantee (NVMe requires it at the LBA format's atomic-write-unit, typically 1 LBA; SATA guarantees it at 512 bytes under normal operation but not on power loss unless the device has PLP). If the sector-write atomicity is violated, ZFS falls back to the previous uberblock slot in the 128-slot array.

This layered approach is why ZFS does not need a journal: the Merkle tree provides structural integrity, the per-block checksum provides data integrity, and the atomic uberblock write provides commit atomicity. Any two of the three failing still leave the pool recoverable to the last-good uberblock txg.

### 4.5 Resilvering and scrub

**Resilver** is the rebuild of a replaced device. On traditional RAID-5/6, rebuild rewrites every sector of the new device (capacity-proportional). On RAID-Z, resilver walks the DMU tree from the MOS down, finds blkptrs that reference the missing DVA, reconstructs from siblings + parity, and writes the reconstructed block to the new leaf. **Time is proportional to allocated data, not raw capacity** — a critical advantage for large, mostly-empty pools.

On dRAID, resilver writes into the distributed spare in parallel across all surviving disks; when a physical replacement is attached, a **rebalance** (incorrectly called "resilver" in some contexts) copies from the spare to the new disk. This decouples "restore redundancy" from "replace the failed disk," so the redundancy restoration happens faster even though the total data moved is larger.

Resilver priority is managed by the `zfs_resilver_min_time_ms` / `zfs_resilver_delay` tunables and the zio priority queue (`module/zfs/vdev_queue.c`). User I/O is prioritized over resilver unless the admin sets aggressive tunables.

**Scrub** is proactively walking every allocated block to verify checksums. Controlled by `zpool scrub <pool>`, status viewable via `zpool status`, throttled by `zfs_scrub_min_time_ms`. Unlike RAID controllers' patrol reads, scrub is **end-to-end** — it verifies the logical content against the parent-stored checksum, not just that the disk returns data. Scheduled commonly via cron or `zed` (the ZFS event daemon). OpenZFS docs "Scrub and Resilver" page is canonical.

### 4.6 RAID-Z expansion

OpenZFS 2.3 (2024) added **RAID-Z expansion** (`zpool attach <pool> <raidz-vdev> <new-disk>`). The operation adds a disk to an existing RAID-Z vdev in place, re-striping existing data over the wider vdev. Crucially, it is **non-destructive and online** — the pool remains available throughout. This was a long-missing feature; historically, to grow a RAID-Z vdev you had to destroy-and-restore from backup.

The expansion walks every allocated block, reads its current stripe, reconstructs it at the new width, and writes it back. Existing blocks keep their original stripe width (recorded in the blkptr) until the next CoW write; only newly written blocks use the full new width. This means capacity gains are gradual — the effective utilization of the new disk's space increases as data is rewritten.

Primary reference: `module/zfs/vdev_raidz.c` (post-2024 code), Mark Maybee's OZDS 2022 and 2023 talks on the expansion design.

**NVFS verdict (§4):** ADAPT mirrors as "replica arenas across devices" (useful for NVFS-over-multi-NVMe). SKIP full RAID-Z / dRAID for M1 — NVFS targets SSDs where device-level parity is typically a vendor feature; parity math can come later. KEEP the "resilver walks allocation metadata, not whole device" property — NVFS's pmap already enumerates live extents, so the equivalent operation is trivial. KEEP the concept of "self-healing on checksum mismatch from a replica" as a future bolt-on once replicated arenas are implemented. ATTACH RAID-Z expansion-style non-destructive arena-widening as a potential future capability once multi-device arenas are implemented.

## 5. Self-healing

### 5.1 Silent corruption background

Bairavasundaram et al. (FAST '08, NetApp study of 1.5 M disks over 41 months) found:

- **~0.5%** of disks experienced at least one **checksum mismatch** per year (i.e. silent corruption detected by NetApp's block-checksum layer).
- SATA disks saw ~4× the rate of enterprise FC disks.
- Corruption events are **correlated within a disk** (temporally and spatially), consistent with firmware bugs or wear events rather than purely random bitrot.
- Corruption is **independent across disks** except for common-cause events (firmware-version-wide bugs), which is what makes RAID + checksums effective.

Panzer-Steindel (CERN, 2007) found in a 33 TB / 3-week test: ~152 corrupt files among 8.7 M, roughly one error per 10^14 bits transferred, broadly consistent with published SATA bit-error rates of 10^14 to 10^15 (vendor datasheets). **[AMBIG]** Different CERN papers and vendor sheets give slightly different error rates; cite the specific paper.

Bonwick's "End-to-End Data Integrity" blog (2005) argues that block-checksum-adjacent-to-block (as in hardware RAID controllers, dm-integrity, NetApp WAFL's per-block checksum) misses the failure modes that matter most — bus errors, firmware misrouting, software bugs — because the adjacent-checksum pair travels together through whatever bad path. The parent-stored checksum is the only layout that catches misdirected writes (data written to wrong LBA) because verification reaches all the way up to the uberblock.

### 5.2 Self-healing read path

On every read, ZFS recomputes the checksum from the returned block and compares against the parent-held value. If it fails:

1. For **mirror**: try each mirror leaf in turn until one passes checksum. Write the good data back to all failed leaves. Account the mismatch as `cksum` errors in `zpool status`.
2. For **RAID-Z / dRAID**: attempt reconstruction using parity + surviving data. Try every combination of surviving columns; this is the "raid-z combinatorial reconstruction" path (`vdev_raidz_combrec`), which can take O(P × choose(N, P)) attempts for P parity. If a reconstruction passes checksum, write the corrected stripe back. If none does, the read fails.
3. For **ditto blocks** (multiple DVAs in one blkptr): try the other DVA slots. Metadata gets 2–3 DVAs by default precisely so that a corrupt metadata block does not take out a subtree.

Source: `module/zfs/vdev_mirror.c` (`vdev_mirror_child_select`), `module/zfs/vdev_raidz.c` (`vdev_raidz_io_done_reconstruct_known`, `vdev_raidz_io_done_reconstruct_unknown`), `module/zfs/zio.c` (`zio_checksum_verified`, `zio_ddt_read_done`).

The self-healing write-back is **opportunistic** — the corrected block is only written back if the vdev is not read-only and the error is on a leaf that the SPA believes is healthy. A suspected-failing device may have writes suppressed to avoid amplifying the failure.

### 5.3 Scrub throttling

Scrubs traverse the entire live blkptr DAG. OpenZFS uses a sorted scrub (`module/zfs/dsl_scan.c`, "sorted scrub" introduced ~OpenZFS 0.8, 2018) that collects blkptrs into a sorted queue and issues I/O in LBA order per vdev, dramatically reducing seek cost on spinning disks. The scrub's progress is persisted (`pool_scan_phys`), so it survives reboots.

Scrub I/O priority is lower than user I/O (`ZIO_PRIORITY_SCRUB`). Tunables (`zfs_scrub_delay`, `zfs_scrub_min_time_ms`, `zfs_scan_idle`) throttle it further under load.

### 5.4 The "bit-rot" framing and its counter-argument

A recurring critique of the ZFS silent-corruption argument (e.g. Andrew Morton's kernel-mailing-list remarks, various btrfs-vs-zfs threads) is that modern ECC RAM + modern SATA/NVMe ECC + modern CPU ECC already catch most of the error modes, so the incremental value of filesystem-level checksums is small. The counter-arguments from Bonwick's 2005 post and the FAST '08 paper:

1. **Misdirected writes** — firmware bugs that write a valid block to the wrong LBA. Hardware ECC is correct (the data on the disk matches the data the disk was asked to write); there is no detection at any layer except parent-held checksum.
2. **Phantom writes** — writes that appear to complete but never reach the platter. Parent-held checksum on the next read catches the stale content.
3. **Buggy in-memory caching between filesystem and device** — e.g. a corrupted page-cache page flushed to disk. Disk-embedded checksums travel with the bad data; parent-held checksums are computed at write-issue time against the corrupted memory so they might also be corrupted. But the **scrub walking from a different memory context** (fresh read of parent + fresh read of child) has a chance to catch it on a subsequent pass.
4. **Bus corruption** not covered by the lower-level protocol CRCs — rare on PCIe, more common historically on parallel SCSI / PATA.

The net empirical answer from FAST '08 is that the rate is low but non-zero (~0.5% of disks/year), and that the rate scales with disk count in data-center deployments to where one or more events per day is routine. For personal-scale use, the rate is low enough that the argument against is "why pay the checksum cost"; for fleet-scale use, the rate makes checksums mandatory.

**NVFS verdict (§5):** KEEP end-to-end checksum verification. KEEP background scrub that walks live blkptrs. KEEP ditto-block concept for metadata (NVFS can replicate pmap-root blocks). ADAPT self-healing to arena-replica model once replicas exist.

## 6. Snapshots and clones

### 6.1 Snapshots

A ZFS snapshot is a **read-only, O(1)-created view of a dataset as of a given txg**. Mechanically, a snapshot is an object set (`dsl_dataset_phys_t`) that pins a root blkptr — the dataset's MOS-pointed root at the moment of snapshot creation. Since CoW means subsequent writes allocate new blocks, the snapshot's blkptrs remain valid forever; the snapshot simply prevents those old blocks from being freed.

Creation path: `dsl_dataset_snapshot_sync` in `module/zfs/dsl_dataset.c`. The snapshot is a DSL dataset object with `ds_prev_snap_obj` linking it into the snapshot chain. Space accounting (`ds_used_bytes`, `ds_referenced_bytes`, `ds_unique_bytes`, `ds_compressed_bytes`, `ds_uncompressed_bytes`) tracks how much of the snapshot's content is unique to it.

Snapshots are accessible at `<mountpoint>/.zfs/snapshot/<name>` (or via `zfs clone`). They are immutable.

### 6.2 Clones

A **clone** is a writable snapshot. `zfs clone src@snap dest` creates a new dataset whose base is the snapshot, to which normal CoW writes can be made. The clone's blkptr tree is initially identical to the snapshot's; writes append new blocks owned by the clone.

A clone has an implicit dependency on its origin snapshot — the snapshot cannot be destroyed while any clone depends on it. `zfs promote <clone>` reverses the parent-child relationship: it makes the clone the "original" and the former original the clone, allowing the former original to be destroyed.

### 6.3 Dead lists and space accounting

Space accounting in the presence of snapshots is non-trivial: when a block is freed in the live dataset, is it actually free, or is it still referenced by a snapshot?

ZFS uses **dead lists**: a per-dataset list of blocks that were freed in the live dataset but are still referenced by at least one snapshot. When a snapshot is destroyed, its dead list is walked and blocks are freed (or moved to the preceding snapshot's dead list). The birth-txg in each blkptr makes this efficient: during a free operation, compare the blkptr's birth txg to the birth txg of the oldest snapshot — if the block was born before that snapshot, it is still referenced.

Source: `module/zfs/dsl_deadlist.c`, `module/zfs/bpobj.c`, `include/sys/dsl_deadlist.h`.

The "space efficient snapshot" property comes from this: snapshots cost only the blocks that diverged after the snapshot was taken, not a full second copy.

### 6.4 `zfs diff` and `zfs hold`

- `zfs diff snap1 snap2` walks the two snapshot trees and emits the per-file changes between them. It uses blkptr birth-txg ordering: any subtree with min-birth-txg > `snap1`'s txg is changed; prune the rest.
- `zfs hold <tag> <snap>` pins a snapshot against destruction, preventing accidental loss during backup pipelines.

### 6.5 Bookmarks

A **bookmark** (`zfs bookmark <snap> <bookmark-name>`) is a lightweight marker that records a snapshot's birth txg and identity **without** pinning the snapshot's blocks. After bookmarking, the snapshot itself can be destroyed, but the bookmark remains and can serve as an incremental-send source. The stream computed from `zfs send -i #bookmark newsnap` is byte-identical to what `zfs send -i snap newsnap` would have produced.

Bookmarks were added in OpenZFS 0.7 (2017) specifically for the replication scenario where an administrator wants to retain "last-known-replicated-point" information without paying the space cost of keeping that snapshot around. Primary reference: `module/zfs/dsl_bookmark.c`, `zfs-bookmark(8)`.

### 6.6 Redacted send / receive

OpenZFS 2.0 (2020) added **redacted send** — a mode in which specific files or file ranges are elided from the send stream, replaced with "redaction records" that identify what was removed. The receiver can materialize a redacted dataset; scrubs still walk the surviving blocks and verify integrity. The use case is GDPR-style data-deletion from replicas: one can produce a replica that is provably missing the specified records without re-sending the entire dataset.

Redaction bookmarks (`zfs redact <snap> <redaction-bookmark> <obj>...`) mark the objects to be redacted; subsequent sends relative to that bookmark elide them. Primary reference: `module/zfs/dmu_redact.c`, OZDS 2019 talk on redacted send.

**NVFS verdict (§6):** KEEP snapshots as "pinned pmap-root blkptr with a birth txg." ADAPT clones as writable pmap-root descendants. KEEP dead-list + birth-txg machinery; it is exactly the arena-GC accounting NVFS needs when multiple pmap roots coexist. KEEP bookmarks (cheap, solve a real operational problem). ATTACH redacted-send as a post-M1 feature — the use case is real but the implementation is non-trivial.

## 7. Deduplication

### 7.1 In-line DDT dedup

ZFS dedup is in-line, block-granular, and cryptographic-checksum-based. When `dedup=on` for a dataset, every write looks up the block's checksum in the **DDT** (deduplication table) before allocating. On hit, the existing block is referenced (`dde_refcount++`); on miss, the block is written and a DDT entry is added.

DDT format: `ddt_entry_t` / `ddt_phys_t` in `include/sys/ddt.h`. Each entry keys on the checksum (one entry per unique block) and stores `{checksum, props, refcount, phys[3]}` where `props` include compression and checksum algorithm IDs (to prevent cross-algorithm aliasing) and `phys` is the DVA(s) where the unique data lives. The DDT is itself a set of ZAP objects stored in the MOS (three ZAP classes: `ddt_zap_ditto`, `ddt_zap_duplicate`, `ddt_zap_unique`).

Writes with dedup=on go through an extra zio pipeline stage (`zio_ddt_write`, `zio_ddt_read_start`, `zio_ddt_collision`). The checksum must be cryptographic; OpenZFS rejects `dedup=on` with non-crypto checksums.

Verify mode (`dedup=sha256,verify`) reads the candidate hit block and byte-compares before decrementing the write. Verify mode defeats hash-collision risk at the cost of a read on every dedup hit.

### 7.2 RAM cost — "the dedup rule"

The classic sizing rule, from Oracle docs (ZFS Administration Guide, Oracle Solaris ZFS Administrator's Manual Appendix A) and Delphix's "DDT sizing" blog posts:

- Each DDT entry is **~320 bytes** on-disk, slightly larger in-memory (approximately 350–400 bytes including ARC overhead). **[AMBIG]** Different sources cite 200–400 bytes per entry; the 320-byte figure is the OpenSolaris default for fletcher4+sha256 entries.
- Each DDT entry corresponds to one **unique block**, i.e. one logical record (typically 128 KiB with default `recordsize`).
- Therefore: for 1 TB of deduped data at 128-KiB blocks with no dedup (worst-case for DDT size), you have `1 TB / 128 KiB ≈ 8 M entries × 320 bytes = 2.5 GB` of DDT.
- Dedup works only if the DDT fits in RAM (or in a fast L2ARC/special vdev). DDT misses cause random 8-KiB reads of DDT metadata per block write, catastrophic for throughput.
- The oft-quoted "1–5 GB RAM per 1 TB of dedup data" covers a range of block sizes and dedup ratios. Oracle and Delphix both warn that dedup requires careful capacity planning; most admins enable dedup only on datasets where the ratio is known to be high.

### 7.3 Why dedup is usually off

From the OpenZFS FAQ and repeated illumos-discuss, freebsd-fs, and zfs-discuss threads 2012–2024: dedup's cost-benefit is terrible unless the dedup ratio is above ~2.0 and the DDT fits in memory. Use cases that clear the bar are narrow (VM disk images, email archives, containers); general-purpose filesystems do not. Alternatives that usually dominate:

- **Compression** (lz4 / zstd) — cheap, always on by default in OpenZFS 2.x.
- **Per-file dedup via snapshots + clones** — if you know objects are related.
- **Application-level dedup** — Restic, Borg, etc., with filesystem-transparent block dedup disabled.

### 7.4 Fast dedup (OpenZFS 2.3+)

The **fast-dedup** proposal, discussed at OZDS 2023 and merged in OpenZFS 2.3 (2024), addresses the DDT RAM cost by:

- Moving most of the DDT out of ARC and into a **log-structured side file** (think "write-optimized hash index on NVMe").
- Allowing per-dataset dedup quotas.
- Adding `zfs dedup` "dedup now" command to reshuffle existing data into the DDT without a full rewrite.
- Relaxing the strict "DDT must fit in RAM" rule while providing predictable latency via the log.

Status per OpenZFS release notes: fast dedup is opt-in and still maturing; the older in-line DDT path remains the default for backward compatibility.

### 7.5 Block cloning (reflink) — an alternative to dedup

OpenZFS 2.2 (2023) added **block cloning**, the `BRT` (Block Reference Table) mechanism that powers `cp --reflink=always` and `copy_file_range()` on ZFS. Instead of copying data, ZFS creates a new logical reference to the source blocks and increments refcounts in the BRT.

Block cloning differs from dedup in key ways:

- **Explicit, not transparent**: triggered by specific syscalls. No table lookup on every write.
- **No write-path cost**: the hot write path is unaffected.
- **No RAM cost at scale**: the BRT is proportional to cloned blocks, not to all unique blocks in the pool.
- **Granularity**: block cloning is at recordsize granularity, same as dedup, but the operation is per-syscall not per-block.

Primary reference: `module/zfs/brt.c`, `include/sys/brt.h`, OZDS 2022 talk by Paweł Jakub Dawidek.

Block cloning covers most of the practical "I want to save space on duplicated data" use cases (VM image copies, container layer copies, source-tree snapshots, backup re-copy) without paying the dedup RAM tax. For most workloads, block cloning + `zfs clone` + compression dominates dedup.

**NVFS verdict (§7):** SKIP in-line dedup as a default. ATTACH as an opt-in feature for specific datasets (capability-probed via admin property). If implemented, follow the fast-dedup model (log-structured side index) rather than the classic RAM-resident DDT. NVFS's arena layout gives us a natural place for the dedup log. **KEEP** block cloning (reflink) — it is the correct default answer for "save space on duplicate data" and is vastly cheaper than dedup.

## 8. Compression

### 8.1 Algorithms

ZFS compression is per-block and per-dataset-configurable. Algorithms (`include/sys/zio.h` enum `zio_compress`):

- **off** — no compression
- **lzjb** — legacy Sun algorithm, ~2× faster than gzip-1 at ~half the compression ratio. Default in older ZFS.
- **gzip-1..gzip-9** — Lempel-Ziv + Huffman, wide compression-ratio tuning. Slow.
- **zle** — zero-length encoding; compresses runs of zeros only. Useful for sparse files.
- **lz4** — LZ4 r127 by Yann Collet. **Default since OpenZFS 0.7 (2017)**. Extremely fast (~1 GB/s/core encode), modest ratio (~1.5–2× on text).
- **zstd** — Facebook's Zstandard. Added in OpenZFS 2.0 (2020). Levels 1..19 (`zstd-1`..`zstd-19`) plus `zstd-fast-N` (N=1..1000). Typical: `zstd-3` matches gzip-6 at ~5× the throughput. `zstd-19` can exceed gzip-9 while being slower.

### 8.2 Early abort

Every write tries to compress. If the compressed size is not smaller than the original by at least one sector (ashift-aligned), the block is stored uncompressed and the `compress=off` flag is recorded in the blkptr. This is the "early abort" short-circuit (`zio_compress_data` in `module/zfs/zio_compress.c`) that keeps compression cost bounded on incompressible data (JPEGs, already-encrypted blobs, random data).

### 8.3 Interaction with dedup

Compression runs **before** dedup checksum. Two identical plaintext blocks compressed with the same algorithm produce the same compressed bytes and therefore the same checksum, so they dedupe. Different compression algorithms produce different compressed bytes, so the DDT stores the compression algorithm ID in the entry to distinguish. (This is why the DDT key is `{checksum, props}`, not just `{checksum}`.)

### 8.4 Interaction with encryption

Encryption runs **after** compression. If you encrypt, then compress, the compression ratio collapses to ~1.0 (encrypted output is near-random). ZFS does compression first, then encryption, which preserves compressibility but leaks information-theoretic hints about plaintext length (standard trade-off, discussed in §13).

### 8.5 Compression level tradeoffs (empirical)

OpenZFS includes published microbenchmarks (in the `tests/zfs-tests/tests/functional/compress/` tree and the `module/zfs/lz4.c` / `module/zfs/zstd/` source comments) that establish approximate ratios:

- **lz4** on mixed text: ~2.1× ratio at ~1.5 GB/s/core compress, ~4 GB/s/core decompress.
- **zstd-3**: ~2.8× ratio at ~500 MB/s compress, ~1.5 GB/s decompress.
- **zstd-9**: ~3.2× ratio at ~100 MB/s compress.
- **zstd-19**: ~3.6× ratio at ~15 MB/s compress, ~1 GB/s decompress (decompression speed is nearly level-independent in zstd).
- **gzip-1**: ~2.5× ratio at ~60 MB/s compress.
- **gzip-9**: ~3.0× ratio at ~20 MB/s compress.

These are order-of-magnitude figures; actual performance depends heavily on data character (JPEGs, already-encrypted, binary blobs compress near 1.0×; source code and JSON often hit 3–5×). **[AMBIG]** Different benchmarks give different numbers; the OpenZFS docs recommend benchmarking on representative data rather than trusting synthetic results.

The practical conclusion from OpenZFS's Performance Tuning guide: **default to lz4** for general use (the write cost is negligible and the space savings are free), escalate to `zstd-3` for datasets where a modest CPU cost buys meaningful space (backups, archives), and reserve `zstd-19` for truly cold data (long-term archive datasets that are written once and read rarely).

**NVFS verdict (§8):** KEEP compression-before-dedup-and-encryption pipeline. KEEP lz4 as default, zstd as opt-in, blake3 as the preferred strong checksum (for dedup-ready datasets). KEEP early-abort.

## 9. Send / receive

### 9.1 Basic send

`zfs send <snap>` produces a byte stream that encodes the snapshot's content. Format documented at OpenZFS "zfs-send(8)" and the "ZFS Send Stream Format" wiki page. The stream is self-describing: `begin`, `object`, `write`, `free`, `end` records with checksums.

### 9.2 Incremental send

`zfs send -i <from-snap> <to-snap>` emits only the blkptrs with `birth > from-snap's txg`. Because blkptrs carry their birth-txg, this is a pruning walk of the DMU tree: any subtree with min-birth-txg ≤ from-snap's birth-txg is skipped. No scan of "what changed" is needed — it falls out of the CoW structure directly.

### 9.3 Replication stream `-R`

`zfs send -R <snap>` emits a stream that recreates the dataset hierarchy, including all descendant datasets, snapshots in birth order, and all dataset properties. `zfs receive -d` on the other side recreates the hierarchy exactly. This is the canonical full-backup / offsite-replica command.

### 9.4 Resumable send

`zfs send -t <token>` resumes a send that was interrupted (e.g. network drop). The receiver records progress and emits a `resume_tok` property on the partially-received dataset; the sender resumes from there. Added in OpenZFS 0.7 (2017).

### 9.5 Raw encrypted send

`zfs send -w` emits the encrypted ciphertext bytes directly, without decrypting and re-encrypting. The receiver stores them as-is, can replicate the dataset without knowing the encryption key, and the stream itself is opaque to anyone without the key. Added in OpenZFS 0.8 (2019) with the encryption feature. Critical for untrusted-backup-target scenarios.

### 9.6 Property inheritance and `zfs receive -o / -x`

Properties set on the source dataset are included in the stream. `zfs receive -o prop=value` overrides on receive; `-x prop` excludes. `zfs receive -u` leaves the received dataset unmounted.

### 9.7 Stream record format (highlights)

The ZFS send-stream format is a self-framing sequence of records, each with a fixed header and variable-length payload. Primary reference: `module/zfs/dmu_send.c` `dump_record`, `include/sys/zfs_ioctl.h` `struct drr_*` types.

Record types (`dmu_replay_record_type_t`):

- `DRR_BEGIN` — stream header, carries pool GUID, dataset GUID, fromsnap/tosnap identification, feature flags, compression hints.
- `DRR_OBJECT` — create or update a DMU object (its dnode).
- `DRR_FREEOBJECTS` — range of object IDs to free.
- `DRR_WRITE` — write a specific block with its payload. For encrypted raw-send, the payload is the ciphertext + IV + MAC; for compressed raw-send, the payload is the compressed bytes.
- `DRR_WRITE_BYREF` — reference a block already in the target dataset (dedup stream, rarely used).
- `DRR_FREE` — free a byte range in an object.
- `DRR_END` — stream terminator with a checksum over the whole stream.
- `DRR_SPILL` — spill-block (large xattr / ACL overflow).
- `DRR_REDACT` — redaction record (§6.6).

Feature flags in the begin record signal what the receiver must support (e.g. `DMU_BACKUP_FEATURE_LZ4`, `DMU_BACKUP_FEATURE_ENCRYPTED_SEND`, `DMU_BACKUP_FEATURE_RAW`). A receiver that does not understand a required feature refuses the stream; backward compatibility is handled by the sender restricting features to what the target supports via `-c` / `-e` / `-L` flags.

Stream integrity is enforced both at the per-record level (each record has a fletcher4 checksum) and at the stream level (the `DRR_END` has an accumulated stream checksum). Corruption during transport is detected at parse time.

**NVFS verdict (§9):** KEEP send/receive wholesale. NVFS's pmap + arena-birth model gives us the same "prune by birth" optimization for incremental. KEEP raw encrypted send (critical for offsite replicas to untrusted targets). ADAPT stream format to NVFS's arena model (stream is a concatenation of arena tails + pmap deltas + root-blkptr updates).

## 10. ZIL (ZFS Intent Log)

### 10.1 What ZIL is for

ZIL handles **synchronous writes** — writes that the application has requested be durable before `write(2)` or `fsync(2)` returns. Asynchronous writes go through the normal txg pipeline (up to 5 seconds of buffering). Synchronous writes cannot wait for the txg; they need to be on stable storage before acknowledgement.

ZIL achieves this by logging the write intent to a dedicated append-only structure. On crash, ZIL replay reconstructs the committed-but-not-yet-synced writes.

Key point: ZIL is **not** a redo log like the main-pool CoW tree. It is a side channel for synchronous intent. Data written via ZIL will still eventually be written to its proper place in the main tree during the next txg sync; the ZIL entries are then free to be recycled.

### 10.2 Record flow

Primary reference: `module/zfs/zil.c`; `include/sys/zil.h`. A synchronous write path:

1. Application calls `write(fd)` with `O_SYNC`, or `fsync(fd)` after an async write.
2. ZPL calls `zil_commit(zilog, oid)` which builds a `lr_write_t` intent record describing the write, appends it to the in-memory ZIL chain, and issues an I/O to the SLOG (if present) or inline log blocks (if absent).
3. `zil_commit` blocks until the write completes (or batches with `zil_commit_waiter`).
4. `write(2)` returns.
5. Later, the next txg sync writes the data to its permanent CoW location. ZIL entries with txg ≤ last-synced are implicitly released.

On crash replay: `zil_replay` walks the ZIL chain (head pointed-to by the object-set header), reconstructs each intent record, and issues the equivalent DMU write. The replayed writes are part of the first post-crash txg.

### 10.3 SLOG (separate log device)

A SLOG is a dedicated log vdev — usually an NVMe SSD with power-loss-protected write cache — attached to the pool via `zpool add <pool> log <device>`. The ZIL uses it exclusively for ZIL writes; the main pool is never written synchronously.

SLOG sizing: a few GB is usually enough (ZIL data is transient, released after txg sync). SLOG latency dominates synchronous-write latency — this is why write-optimized NVMe (Optane, ZNS PLP-cached) or NVDIMM-N SLOGs give such outsized performance improvement for synchronous workloads (NFS sync, databases on ZFS).

Mirroring SLOGs is strongly recommended because a SLOG failure during a crash loses in-flight synchronous writes. OpenZFS 2.x includes heuristics to survive SLOG loss non-destructively on clean shutdown, but not on crash.

### 10.4 `sync=` property

`zfs set sync=<standard|always|disabled>`:

- **standard** (default) — sync writes go through ZIL; async writes go through the txg pipeline.
- **always** — every write goes through ZIL, even async. Useful for NFS semantics.
- **disabled** — sync writes are treated as async. **Dangerous**: the application believes the write is durable after `write()` returns, but it is not. Only safe for workloads that can recover from crash — almost never for a general filesystem.

### 10.5 O_DSYNC, O_SYNC, FUA, and Flush

POSIX `O_SYNC` (file data + metadata durable) and `O_DSYNC` (file data durable, metadata best-effort) both map to ZIL-backed writes in ZFS. The distinction is at the ZPL level — `O_SYNC` forces a more comprehensive ZIL record, `O_DSYNC` can elide some metadata updates.

NVMe FUA (Force Unit Access) is a per-command hint that the command must reach non-volatile media before completing. ZFS issues FUA on ZIL writes when the underlying device supports it, avoiding a subsequent cache flush. When FUA is unavailable (older SATA), ZFS falls back to post-write `FLUSH_CACHE`.

Primary reference: `module/zfs/zil.c` (`zil_commit_writer`, `zil_itx_assign`), `module/os/linux/zfs/zvol_os.c` (FUA handling), NVMe Base Spec 2.0c §6 (Write command, FUA bit).

### 10.6 ZIL is not a performance panacea

Common misconception: "ZIL = write cache." It is not; ZIL is only used for sync writes. Async writes never touch ZIL. A SLOG won't speed up async workloads; only sync-heavy workloads (NFS, databases, some iSCSI clients) benefit.

The OpenZFS docs "ZIL" page, and Brandon Gross's "The ZIL isn't a write cache" blog (mirrored on various ZFS admin sites), are the canonical clarifications.

### 10.7 Indirect ZIL (write to pool if no SLOG)

Without a dedicated SLOG, ZIL records are written to the same pool as normal data, but to **dedicated ZIL blocks** allocated by the SPA from a reserved allocator class. Two sub-modes:

- **Immediate ZIL** (small writes, default `zfs_immediate_write_sz=32 KiB`): the write data is embedded in the ZIL record itself. Efficient for small sync writes.
- **Indirect ZIL** (large writes): the write data is written to a normal pool block (future home), and the ZIL record stores only a blkptr to it. On crash replay, the block is already in place; the ZIL pointer bridges it into the current DMU state.

The immediate/indirect split optimizes the common case: small sync writes (database WAL, NFS metadata) get a single write; large sync writes (big file fsync) avoid a double-write by placing the block directly at its final location.

Primary reference: `module/zfs/zil.c` `zil_commit_writer`, `zfs_log.c` `zfs_log_write`.

### 10.8 ZIL records and DMU types

ZIL records are typed by the operation they describe (`lr_t` in `include/sys/zil.h`): `TX_CREATE`, `TX_MKDIR`, `TX_WRITE`, `TX_TRUNCATE`, `TX_SETATTR`, `TX_REMOVE`, `TX_LINK`, `TX_RENAME`, `TX_ACL`, `TX_WRITE2` (compressed), `TX_CLONE_RANGE` (block clone). Replay of a `TX_WRITE` reconstructs the data write; replay of a `TX_CREATE` re-creates a file with its attributes. This typed-record format is what gives ZIL replay its correctness — replay is not just "re-execute I/O," it is "re-execute the semantic operation."

**NVFS verdict (§10):** KEEP ZIL as a separate arena class — NVFS's existing "append-only intent log" matches almost perfectly. KEEP sync=standard/always/disabled property semantics. ADAPT SLOG as "assign the intent-log arena to a fast device" (NVFS capabilities already support device affinity). KEEP FUA usage. KEEP the typed-record / semantic-replay format; it makes replay auditable and correct.

## 11. ARC and L2ARC

### 11.1 ARC — Adaptive Replacement Cache

The ARC is ZFS's in-memory block cache. Based on Megiddo and Modha (IBM Research, FAST '03), "ARC: A Self-Tuning, Low Overhead Replacement Cache." ZFS's implementation: `module/zfs/arc.c`, `include/sys/arc.h`.

Core design: four queues — **MRU** (Most Recently Used), **MFU** (Most Frequently Used), **MRU-ghost** (evicted from MRU, tracked by key only), **MFU-ghost** (evicted from MFU, tracked by key only). A self-balancing parameter `p` (size of MRU relative to total cache) adapts to workload: a hit in MRU-ghost steals capacity from MFU; a hit in MFU-ghost steals from MRU. This captures both recency and frequency without requiring a heuristic.

The ARC caches **decompressed** (and decrypted) blocks by default. The "compressed ARC" feature (OpenZFS 0.7, 2017) added the option to cache compressed blocks, saving RAM at the cost of CPU on every read. Compressed ARC is the default today for most pools.

### 11.2 ARC tuning and pressure

- `zfs_arc_max` — hard cap on ARC RAM usage (Linux: default is half of system RAM; FreeBSD: similar; illumos: "most of" the unused RAM).
- `zfs_arc_min` — soft floor.
- Linux memory pressure: ARC is registered as a shrinker; on kernel memory pressure, ARC shrinks via `arc_shrink_cb`. The interaction between ARC and the Linux page cache is notoriously tricky (see e.g. the `zfs_arc_sys_free`, `zfs_arc_shrinker_limit` tunables).
- FreeBSD: the ARC is integrated with the UMA (Universal Memory Allocator) and the VM subsystem.

### 11.3 L2ARC

L2ARC is a **second-level, on-SSD read cache**. `zpool add <pool> cache <device>` attaches it. Blocks evicted from ARC may be copied (async, throttled) to L2ARC before being discarded from RAM; subsequent reads check ARC → L2ARC → disk.

Key properties:

- L2ARC is a pure read cache. No write-caching (unlike traditional "bcache"-style L2 caches).
- Entries are tracked by **key + pointer to L2ARC location**. The keys live in ARC (a "headers" list). A large L2ARC can consume significant ARC RAM for its headers (~88 bytes per L2ARC block). Sizing rule: "L2ARC headers cost ~1% of L2ARC size in ARC RAM."
- L2ARC fill rate is throttled (`l2arc_write_max`, default 8 MiB/s) to preserve SSD endurance. For some workloads this is too conservative; `l2arc_write_boost` allows bursts.
- L2ARC miss cost is a disk read; L2ARC hit cost is an SSD read. The break-even depends on the ratio of L2ARC hits to ARC hits.

### 11.4 Persistent L2ARC (OpenZFS 2.0+)

Classic L2ARC was ephemeral — reboot discarded it because the ARC-header keys were in RAM only. **Persistent L2ARC** (OZDS 2019 talk by George Amanakis, merged OpenZFS 2.0) persists the L2ARC key index on the SSD itself, so a reboot repopulates ARC headers from the SSD, making the cache warm immediately.

Trade-off: persistent L2ARC requires writing key-index metadata to the SSD (small but present), increases SSD wear slightly, and adds import-time overhead. It is enabled per-cache-vdev and is default-on in recent OpenZFS.

### 11.5 ARC vs OS page cache

ZFS maintains its own cache (ARC) rather than piggybacking on the OS page cache because:

1. ARC keys by `{blkptr, dva}` not by `{inode, offset}`, which is required to correctly cache post-dedup / post-decompression / post-decryption blocks.
2. ARC needs the self-balancing MRU/MFU semantics that the OS page cache does not provide (OS caches are typically LRU or FIFO).
3. ARC survives dataset remount / snapshot / clone, which OS page cache does not guarantee.

On Linux, this dual caching is a known inefficiency: buffered `read(2)` copies from ARC into the Linux page cache, doubling RAM usage for the same block. `primarycache=metadata` on a dataset reduces this, as does the newer Linux page-cache-bypass for ZFS that some distributions ship.

### 11.6 primarycache and secondarycache properties

Per-dataset properties `primarycache={all|metadata|none}` and `secondarycache={all|metadata|none}` control what is cached in ARC and L2ARC respectively:

- `primarycache=metadata` caches only metadata in ARC. Useful for very large datasets where data cache-hit rate is near-zero (e.g. scratch volumes) — avoids polluting ARC with one-hit-wonder data blocks.
- `primarycache=none` disables ARC entirely for the dataset. Rare; used for raw-zvol workloads where the consumer has its own cache.
- `secondarycache=metadata` on a dataset still allows data in ARC but keeps only metadata in L2ARC, reducing L2ARC wear and header-RAM cost.

### 11.7 Arc_adapt and Kernel/ARC interaction

The `arc_adapt_thread` in `module/zfs/arc.c` runs continuously, observing memory pressure (`arc_need_free`, `zfs_arc_sys_free`, kernel shrinker callbacks) and adjusting ARC size in response. Linux integration is notoriously fraught: the kernel's `/proc/meminfo` reports ARC as "application memory" (part of Used, not Cached or Buffers), which surprises administrators reading memory-utilization dashboards. FreeBSD integrates ARC via UMA more transparently.

Memory pressure response is:

1. Slow shrink via `arc_reclaim_thread` aiming for `arc_c` target.
2. Aggressive shrink when `arc_need_free` > 0, driven by kernel shrinker callback.
3. Eviction is MRU-then-MFU-aware: the adaptive `p` parameter determines which list loses capacity.

**NVFS verdict (§11):** KEEP ARC's MRU/MFU + ghost-list design; NVFS's cache manager can use it directly. NVFS runs in user-space, so the "ARC vs kernel page cache" competition does not apply — NVFS owns the cache, period. KEEP L2ARC as "SSD read-cache arena" with capability probe. KEEP persistent L2ARC index. KEEP primarycache / secondarycache per-dataset knobs; they are cheap and solve real operational problems.

## 12. Allocator, metaslabs, and allocation classes

### 12.1 Metaslabs

A top-level vdev is subdivided into **metaslabs** — typically 200 per vdev, each sized a few GB to a few hundred GB. Each metaslab has:

- A **space map** (on-disk log of alloc/free operations, `space_map_phys_t`)
- An in-memory **range tree** (AVL-tree of free extents)

Metaslabs are loaded on-demand when the allocator needs to place a write; the space map is replayed to build the range tree. This is why large-pool import times are dominated by metaslab load (mitigated by the **space map log**, `zfs_spacemap_log`, OpenZFS 0.8+, which batches space-map updates).

Allocator strategy: `module/zfs/metaslab.c`, `vdev_allocate`. Weighted selection of metaslabs by free space, fragmentation, and least-recently-used. Within a metaslab, first-fit by default; best-fit for large allocations.

Fragmentation tracking is explicit: `zpool list -v` reports a `FRAG%` per vdev. ZFS does not defragment (fundamentally incompatible with CoW over a snapshot chain); the recommended response to high fragmentation is "use more capacity" or "re-create the pool from a send stream."

### 12.2 ashift

`ashift` is the log2 of the minimum allocation size (i.e. the sector size the SPA treats as the atomic unit). `ashift=9` → 512 B sectors; `ashift=12` → 4 KiB sectors; `ashift=13` → 8 KiB.

Critical: `ashift` is set at **vdev creation time** and cannot be changed. Choosing the wrong ashift (e.g. 9 on a 4K-native disk that lies about its sector size) cripples performance (4× write amplification at the SPA layer). The safe default on modern disks is `ashift=12`; on NVMe, check `nvme id-ns` `lbafs` for the native block size (often 4096, sometimes 512, occasionally 16384).

Primary reference: `zpoolprops(7)` `ashift` property; `module/zfs/vdev.c` `vdev_ashift_optimize`.

### 12.3 Allocation classes

OpenZFS supports per-class allocation via specialized vdevs:

- **special** — metadata + "small blocks" (`special_small_blocks` property sets the threshold). A pool with a `special` vdev keeps metadata and small files on fast storage while bulk data goes on slow bulk vdevs. Added OpenZFS 0.8.
- **dedup** — DDT lives here. Added OpenZFS 0.8.
- **log** (SLOG) — ZIL only. §10.
- **cache** (L2ARC) — §11.

The allocation class is set per-I/O by the SPA based on object type (metadata → special, DDT → dedup, etc.). Missing a specialized vdev simply falls through to the normal top-level vdevs.

Loss of a `special` vdev is fatal (takes out all metadata); mirror it.

### 12.4 Space-map log

The per-metaslab space map is append-only; each txg's allocations and frees append log entries. Once the log exceeds a threshold, the metaslab is "condensed" — the log is replaced by a compacted range-tree snapshot. This keeps space-map load time bounded.

Primary reference: `module/zfs/space_map.c`, `include/sys/space_map.h`.

### 12.5 Metaslab selection heuristics

`metaslab_alloc_dva` is the entry point. For each allocation:

1. Filter metaslabs by allocation class (normal / special / dedup / log).
2. Weight metaslabs by free space and fragmentation. The weight is a 64-bit value encoding `(fragmentation_score, free_space, allocation_group_LRU)` such that `argmax` selects the best candidate.
3. Within the chosen metaslab, descend the range tree using first-fit (default) or best-fit (for allocations > `metaslab_force_ganging` threshold).
4. If the metaslab can't satisfy, fall through to the next-best.
5. If no metaslab can satisfy, fall back to **gang blocks** (§2.6) as the last resort.

Per-txg metaslab budgets prevent one metaslab from being hammered while others stay cold. Metaslab LRU ensures hot data clusters into a small number of metaslabs rather than spreading across the entire vdev, improving read locality.

### 12.6 Space map encoding

The on-disk space map is a sequence of `space_map_entry_t` records (bit-packed in OpenZFS 0.8+'s compact format, `SM2`). Each record encodes `{alloc|free, run_length, offset}`. Replay of the log reconstructs the free-space bitmap; condensation collapses the log into a fresh base image when the log exceeds `zfs_condense_pct` of the metaslab size.

Primary reference: `module/zfs/space_map.c`, `include/sys/space_map.h`.

**NVFS verdict (§12):** KEEP metaslab → arena analogy; each NVFS arena already has an allocation-class tag. KEEP ashift equivalent; NVFS already probes device LBA size. ADAPT the "special / dedup / log / cache" vdev classes as NVFS arena classes (already in the NVFS design). KEEP space-map log design for allocation metadata. KEEP the metaslab weighting heuristic; NVFS's arena selector should use analogous fragmentation + free-space + LRU terms.

## 13. Native encryption

### 13.1 Feature overview

Native ZFS encryption was merged in OpenZFS 0.8 (2019); design and review talks at OZDS 2016 and OZDS 2017 (Tom Caputi, Datto). Primary reference: `module/zfs/zio_crypt.c`, `module/zfs/dsl_crypt.c`, `include/sys/zio_crypt.h`, `include/sys/dsl_crypt.h`.

### 13.2 What is encrypted

- **Data blocks** — file contents, directory contents, xattr payloads.
- **Non-sensitive metadata** is **not** encrypted: block pointers (DVAs, checksums, birth times), dataset names, snapshot names, property names. This allows raw send/receive of encrypted datasets without the key (§13.5).

The encrypted blkptr format stores the IV (96-bit nonce) and the MAC (96-bit authentication tag) inside the blkptr's checksum field. The block payload itself is AES-CCM ciphertext. This is why encrypted datasets must use `checksum=sha256` or later — fletcher4 has no room to carry the MAC.

Algorithms: **AES-GCM** (128 / 256 bits) — default is `aes-256-gcm`; **AES-CCM** (128 / 256 bits). Listed in `zfsprops(7)` `encryption=` property.

### 13.3 Key hierarchy

Three-level key hierarchy:

1. **User key** — the key material the user supplies: passphrase (PBKDF2-derived), raw 256-bit hex, or raw bytes from a keyfile (`keyformat=passphrase|hex|raw`, `keylocation=prompt|file://|https://`).
2. **Wrapping key** — derived from the user key (HKDF). Wraps the master key.
3. **Master key** — randomly generated per-dataset at creation; wraps the **data keys**.
4. **Data keys** — one per txg or per-object-set block range; rotated automatically by the SPA to limit IV reuse.

User key changes (`zfs change-key`) rewrap the master key; they do not re-encrypt data. Re-encryption requires a full send/receive into a new encrypted dataset.

Encryption roots: a dataset can either have its own keys (`encryptionroot=<self>`) or inherit from an ancestor. Inheritance is crucial for bulk management.

### 13.4 Raw send/receive with encrypted datasets

`zfs send -w <encrypted-snap>` emits the ciphertext bytes without decrypting. The receiver does not need the key; it stores the ciphertext unchanged. The data is opaque at the receiver (until the key is loaded), but scrubs and replication still work because all checksums and MACs are verified by blkptr, not by plaintext content.

This is the feature that makes "untrusted offsite backup" a first-class ZFS scenario.

### 13.5 What is not protected

- **Metadata confidentiality**: dataset names, snapshot names, property names, allocation patterns are visible on disk and in send streams.
- **Access-pattern leakage**: block sizes, offsets, timings leak information about plaintext structure.
- **Deduplication on encrypted datasets**: possible only within a single encryption root (keys must match for ciphertext to match). `dedup=on` + `encryption=on` dedup across datasets only when they share a master key. Per-dataset-master-key datasets don't dedup cross-dataset.

### 13.6 IV management

AES-GCM requires a unique IV per key per encryption. ZFS generates the 96-bit IV deterministically from `{master_key_id, object_id, block_offset, birth_txg}`, which guarantees uniqueness within the lifetime of a single master key. Master key rotation (forced rotation after a configurable number of encryptions, or explicit admin action) keeps IVs from wrapping.

The deterministic IV scheme is important for raw send/receive: the same plaintext, written at the same object offset and same birth-txg under the same master key, produces identical ciphertext. This is why raw-send streams are byte-identical across receiver copies (critical for replicated-backup checksumming) and why key-changes require full data rewrite (IV space tied to key rotation count).

Primary reference: `module/zfs/zio_crypt.c` `zio_crypt_encode_iv`, `zio_crypt_generate_iv`.

### 13.7 Known limitations

- **No authenticated metadata**: DVAs, checksums, and birth-txg in blkptrs are unencrypted and unauthenticated. An attacker with write access to the device can rewrite the pool's topology even if they cannot read data. Mitigated in practice by the parent-held MAC (rewritten metadata won't authenticate on the next read up the tree), but not formally guaranteed.
- **No deniable encryption**: the presence and structure of encrypted datasets are visible.
- **Key-compromise reexposes data**: once a master key is leaked, all ciphertext under that master key is readable. Key rotation does not re-encrypt existing data; it only changes future encryption. To force re-encryption, do `zfs send | zfs receive` to a new encryption root.

**NVFS verdict (§13):** KEEP native encryption as a core feature, matching ZFS's three-level key hierarchy and inheritance model. KEEP MAC-in-checksum layout (it is the only clean way to carry authenticated encryption per block). KEEP raw send/receive. Use AES-256-GCM as default with ChaCha20-Poly1305 as an option (NVFS target CPUs include ARM and RISC-V where ChaCha may beat AES). KEEP deterministic IV generation (it is the enabler for raw send).

## 14. Scrub, resilver, repair (detail)

Covered structurally in §4.5 and §5. Additional operational detail:

### 14.1 Priority and throttling

zio priority classes in `include/sys/zio.h`:

- `ZIO_PRIORITY_SYNC_READ` — user-facing sync read, highest
- `ZIO_PRIORITY_SYNC_WRITE` — user-facing sync write
- `ZIO_PRIORITY_ASYNC_READ` — readahead
- `ZIO_PRIORITY_ASYNC_WRITE` — txg-sync write
- `ZIO_PRIORITY_SCRUB` — scrub/resilver, lowest
- `ZIO_PRIORITY_REMOVAL` — device removal rewrite

The vdev queue (`module/zfs/vdev_queue.c`) maintains per-priority FIFOs and aggregates adjacent I/O. Scrub/resilver are preempted by user I/O.

Tunables for user-vs-scrub balance: `zfs_scan_idle`, `zfs_scan_min_time_ms`, `zfs_scrub_min_time_ms`, `zfs_scrub_delay`, `zfs_resilver_min_time_ms`, `zfs_resilver_delay`.

### 14.2 Sorted scrub

Pre-0.8 scrub walked blkptrs in DMU tree order, which on spinning disks produced a random-IO seek storm. Sorted scrub (OpenZFS 0.8, 2018) queues blkptrs into a memory buffer sorted by DVA, then issues them in LBA order per leaf vdev. Seek cost drops roughly 10×. Progress is checkpointed so the sort doesn't have to restart on crash.

### 14.3 TRIM interactions

ZFS supports both **manual TRIM** (`zpool trim <pool>`) and **autotrim** (`autotrim=on` pool property, OpenZFS 0.8+). Autotrim issues `UNMAP`/`TRIM` commands to the device as blocks are freed by the syncing txg.

Autotrim is opt-in because on some older SSDs TRIM is synchronous-on-each-command and hurts performance; on modern NVMe, autotrim is generally a net win. See `module/zfs/vdev_trim.c` and `zpool-trim(8)`.

Manual `zpool trim` walks all free space and issues TRIM commands in sorted LBA order. This is useful after a bulk delete or as a periodic maintenance.

### 14.4 Device removal

`zpool remove <pool> <vdev>` (OpenZFS 0.8+) allows removing a top-level vdev from a pool by rewriting its allocations onto remaining vdevs. The rewrite is logged (`indirect_vdev`) so that blkptrs continue to dereference correctly after the physical vdev is gone.

Device removal is supported for mirror and single-disk vdevs; **not** for RAID-Z / dRAID (the parity would have to be recomputed across remaining vdevs with different geometry).

Primary reference: `module/zfs/vdev_removal.c`, `zpool-remove(8)`.

### 14.5 zio pipeline stage order

The zio pipeline (`module/zfs/zio.c` `ZIO_PIPELINE_*` tables) encodes the order of transformation stages applied to every I/O. Write pipeline in simplified order:

1. `ZIO_STAGE_OPEN` — allocate and initialize zio state.
2. `ZIO_STAGE_READ_BP_INIT` / `ZIO_STAGE_WRITE_BP_INIT` — prepare blkptr fields, pick DVAs if allocating.
3. `ZIO_STAGE_ISSUE_ASYNC` — schedule on the appropriate taskq if not already on one.
4. `ZIO_STAGE_WRITE_COMPRESS` — compression (if enabled and beneficial).
5. `ZIO_STAGE_ENCRYPT` — encryption (if enabled).
6. `ZIO_STAGE_CHECKSUM_GENERATE` — compute checksum over the post-compress-post-encrypt bytes.
7. `ZIO_STAGE_DDT_WRITE` — dedup lookup + refcount (if enabled).
8. `ZIO_STAGE_NOP_WRITE` — detect "identical-to-existing" writes and skip allocation.
9. `ZIO_STAGE_DVA_ALLOCATE` — pick a DVA on a vdev via metaslab allocator.
10. `ZIO_STAGE_DVA_THROTTLE` — backpressure on per-vdev write-queue depth.
11. `ZIO_STAGE_VDEV_IO_START` / `ZIO_STAGE_VDEV_IO_DONE` — issue to vdev, wait for completion.
12. `ZIO_STAGE_CHECKSUM_VERIFY` — (read path) verify checksum; issue reconstruction zios if failed.
13. `ZIO_STAGE_DONE` — completion callback to parent zio / waiter.

The pipeline is explicit and data-driven: each zio is a state machine advancing through stages, with stages gated by dependencies (e.g. VDEV_IO_START cannot run before DVA_ALLOCATE). This model is what makes ZFS's I/O subsystem auditable — the exact transformations applied to a block are a function of its pipeline mask.

Scrub-initiated zios use a modified pipeline that includes CHECKSUM_VERIFY without VDEV_IO_START (verify-only) and, on failure, fork a repair zio with the normal write pipeline.

Primary reference: `module/zfs/zio.c` `zio_execute`, `zio_wait_for_children`, and the `ZIO_*_PIPELINE` tables.

### 14.6 I/O aggregation

The vdev-queue layer aggregates adjacent in-flight I/Os before dispatching to the device: if two outstanding reads target contiguous LBAs, they are merged into one larger read. Controlled by `zfs_vdev_aggregation_limit` (default 1 MiB for spinning disks, smaller for SSDs).

Aggregation is especially effective for scrub on spinning disks (adjacent blkptrs often land at adjacent DVAs after txg-sync-coalescing) and for streaming reads (read-ahead prefetcher issues many sequential I/Os). On NVMe, aggregation is less useful because the device's internal queueing already handles it; OpenZFS auto-tunes the limit lower for NVMe.

**NVFS verdict (§14):** KEEP sorted scrub (arena-LBA-order walk). KEEP TRIM / UNMAP integration; NVFS already has arena-discard. KEEP device removal via indirect remap; NVFS's pmap supports this naturally. KEEP explicit zio pipeline stage model; NVFS's I/O scheduler should use the same stage-machine approach. KEEP I/O aggregation; trivial to add and essential for spinning-disk scrub.

## 15. Failure modes and recovery

### 15.1 Pool import

At import (`zpool import`), ZFS:

1. Reads the labels from every candidate vdev.
2. Assembles the vdev tree from the highest-txg label.
3. Validates `ub_guid_sum` matches the sum of all vdev GUIDs in the config — if a vdev is missing, the sum won't match.
4. Reads the MOS root blkptr from the chosen uberblock.
5. Walks the MOS to find datasets, DDT, ZIL heads, etc.
6. Replays ZIL for each dataset with a non-empty ZIL.
7. Mounts datasets (unless `-N`).

Import options:

- `-f` — force import, override hostid check. Dangerous if the pool is in use by another host.
- `-F` — rewind. If the current uberblock is damaged or imports inconsistent, walk back through older uberblocks.
- `-T <txg>` — import as of a specific txg, rewinding further.
- `-o readonly=on` — import read-only.
- `-X` — extreme rewind; combined with `-F`, walks back much further than default.

### 15.2 spa_load_verify

On import (and especially after `-F`), `spa_load_verify` walks the MOS and a sample of blkptrs to verify consistency before completing the import. If verification fails, the import is rolled back to an earlier uberblock.

Primary reference: `module/zfs/spa.c` `spa_ld_verify_pool_data`, `spa_ld_verify_checkpoint`.

### 15.3 zdb forensic tool

`zdb(8)` is the ZFS debugger: direct MOS inspection, blkptr dumps, dnode trees, dataset internals. Read-only, does not modify the pool. Essential for diagnosing corruption that won't import normally.

Commands (partial):

- `zdb -l <device>` — dump labels from a device
- `zdb <pool>` — dump pool config
- `zdb -d <pool>/<dataset>` — dump dataset's dnodes
- `zdb -u <pool>` — dump uberblock array from active label
- `zdb -e <poolname>` — import-exempt mode, read a pool that cannot be imported
- `zdb -bbbb <pool>` — deep consistency check of all blkptrs

### 15.4 zpool clear and transient errors

`zpool clear <pool> [<vdev>]` clears the error counters and, if the vdev has been marked FAULTED/DEGRADED due to transient errors, attempts to re-online it. It does not repair data; scrub does that.

### 15.5 What cannot be recovered

- **Rollback past the commit-only-ever-retained txg window**: ZFS retains a small number of uberblocks (128 per label × 4 labels, but many are stale). Beyond that, no older root is available. Catastrophic metadata corruption + a crash that burns through all 128 slots = pool dead.
- **Loss of a non-redundant vdev**: if a top-level vdev has no mirror/parity and is lost, the pool is dead (data striped across top-level vdevs means any missing top-level loses its share).
- **Loss of the `special` vdev in a pool that has one**, without mirror: fatal.
- **Overwritten uberblocks with mismatched GUID sum**: rare but possible if someone `dd`s into the device by mistake.
- **ZIL replay failure on a pool with sync=always + crashed SLOG loss**: the most-recent synchronous writes are gone even though the main-pool data is intact, because ZIL replay reconstructs those writes from the SLOG that just died.

### 15.6 Scrub vs resilver vs repair

- **Scrub** — proactive, walks the live tree, verifies, self-heals where possible.
- **Resilver** — reactive, rebuilds a replaced/attached device.
- **Repair (implicit on every read)** — §5.2, the self-heal that happens during normal I/O.

### 15.7 Pool checkpoint

OpenZFS 0.8 (2019) added **pool checkpoint** (`zpool checkpoint <pool>`): a snapshot of the **entire pool**, not just a dataset. The checkpoint pins the current uberblock such that any destructive pool-level operation (feature upgrade, dataset destroy, administrative mistake) can be rolled back by `zpool checkpoint --discard <pool>` → `zpool export` → `zpool import --rewind-to-checkpoint`.

The checkpoint mechanism walks every metaslab at checkpoint time, marking all currently-allocated blocks as "retained-at-checkpoint" so they are not freed even if the live tree releases them. This is expensive in terms of space (the pool cannot reclaim any block freed after checkpoint) and checkpoint takes pool-wide locking during create/discard, so it is not a replacement for snapshots; it is a "belt-and-suspenders" tool for risky administrative operations.

Primary reference: `module/zfs/spa_checkpoint.c`, `zpool-checkpoint(8)`.

### 15.8 Failmode policy

The `failmode` pool property controls behavior when the pool becomes unreachable (all vdevs failed or I/O errors exceeding `zpool_min_iops_fail` threshold):

- `wait` (default) — block all I/O indefinitely. Administrator must intervene. Safe default because it prevents silent data loss but blocks the calling process.
- `continue` — return `EIO` to user processes, keep trying device I/O. Useful when the workload can tolerate transient errors.
- `panic` — kernel panic. Useful in clustered failover scenarios where a reboot is preferable to continued degraded operation (HA clusters).

Primary reference: `module/zfs/spa.c` `spa_io_failure_mode`.

### 15.9 MMP — Multi-Host Protection

MMP (Multi-Modifier Protection, sometimes called Multi-Host Protection, `zpool set multihost=on`) periodically writes a "heartbeat" record to a random uberblock slot, stamped with the host's GUID. On import, ZFS watches the heartbeat slot for a configured interval; if the heartbeat advances during that window, it means another host has the pool imported and import refuses (override via `-f`, but with loud warning).

This is ZFS's defense against accidental dual-imports in shared-storage (iSCSI, FC, dual-attached SAS) scenarios, which would otherwise silently corrupt the pool by interleaving txg writes from two hosts.

Primary reference: `module/zfs/mmp.c`, `zpool-import(8)` `multihost` section.

**NVFS verdict (§15):** KEEP uberblock-rotation rewind. KEEP `zdb`-style forensic tool (NVFS needs one early). KEEP read-only import mode. KEEP pool-level checkpoint (for risky admin ops). KEEP failmode policy (administrators want the choice). ATTACH MMP-style multi-host protection when NVFS is used over shared storage (not urgent for M1 user-space-on-local-NVMe). DESIGN-NOTE: NVFS's multi-root pmap history already supports rewind; the operational interface should match `zpool import -T txg` closely.

## 16. NVFS translation table

For each ZFS feature, verdict: **KEEP** (copy wholesale), **ADAPT** (take the idea, rework for NVFS), **SKIP** (not applicable or deliberately omitted), **ATTACH** (capability-probe, optional bolt-on).

| ZFS feature | §ref | NVFS verdict | Notes |
|---|---|---|---|
| SPA/DMU/ZPL/ZIL layering | §2.1 | KEEP | Maps onto MDSOC axes cleanly |
| Top-level vdev pool + dynamic striping | §2.2 | ADAPT | Arenas instead of vdevs; striping is per-arena-class |
| Label rotation (L0–L3) | §2.3 | ATTACH | Only when we control physical device layout; on a file-backed NVFS, only L0+L1 make sense |
| Uberblock array + rotation | §2.4 | KEEP | Already in the NVFS pmap-root design |
| Transaction groups (txg) | §2.5 | KEEP | NVFS's "arena seal + publish" is the same pattern |
| Block pointers (blkptr) | §2.6 | ADAPT | NVFS's pmap entry is the blkptr equivalent; widen it to carry the child checksum |
| Indirect blocks | §2.7 | KEEP | Needed for large objects |
| Ditto blocks (multi-DVA) | §2.6 | ADAPT | "Replicate metadata across arenas" already in the NVFS arena model |
| Fletcher4 + blake3 checksums | §2.8 | KEEP | blake3 as the default strong checksum |
| CoW everywhere | §3.1 | KEEP | Foundational |
| Merkle-tree integrity | §3.3 | KEEP | Foundational |
| Three-phase txg (open / quiesce / sync) | §3.2 | KEEP | Matches NVFS's arena-commit pipeline |
| Mirror vdevs | §4.2 | ADAPT | "Replica arenas" once multi-device support is in |
| RAID-Z1/Z2/Z3 | §4.1 | SKIP (M1) | Parity math is tangential to NVFS's first-milestone scope; device-level parity is adequate initially |
| dRAID | §4.3 | SKIP (M1) | Same reasoning |
| Self-healing read | §5.2 | ADAPT | Works for replicated arenas; no analogue for single-arena |
| Sorted scrub | §4.5, §14.2 | KEEP | Walk pmap in arena-offset order |
| Resilver = walk of allocation metadata | §4.5 | KEEP | Already trivial given pmap |
| Silent-corruption detection on read | §5 | KEEP | Per-block checksum verify on read is mandatory |
| Snapshots (pinned root) | §6.1 | KEEP | pmap-root pin |
| Clones (writable snapshot) | §6.2 | KEEP | Writable pmap descendant |
| Dead lists + birth-txg | §6.3 | KEEP | Arena-GC accounting |
| `zfs diff`, `zfs hold` | §6.4 | KEEP | Useful operational tools |
| In-line DDT dedup | §7.1–7.3 | SKIP (default) | Off by default; fast-dedup-style opt-in |
| Fast dedup (log-structured DDT) | §7.4 | ATTACH | If dedup is enabled, use log-structured side index |
| lz4 / zstd / zle compression | §8 | KEEP | lz4 default, zstd opt-in |
| Early-abort compression | §8.2 | KEEP | Free |
| Compress → encrypt order | §8.4, §13.2 | KEEP | Standard |
| Send / receive | §9 | KEEP | pmap-delta + arena-tail stream |
| Incremental via birth-txg prune | §9.2 | KEEP | Trivial given birth-txg |
| Resumable send | §9.4 | KEEP | Required for long replication |
| Raw encrypted send | §9.5 | KEEP | Untrusted-backup-target scenario |
| ZIL | §10.1–10.2 | KEEP | NVFS's intent-log arena is the ZIL equivalent |
| SLOG = separate-device log | §10.3 | ADAPT | Intent-log arena on a designated fast device |
| sync= standard/always/disabled | §10.4 | KEEP | Per-dataset property |
| NVMe FUA for ZIL | §10.5 | KEEP | Already capability-probed in NVFS |
| ARC (MRU/MFU + ghosts) | §11.1 | KEEP | NVFS cache manager runs in user-space; no page-cache fight |
| Compressed ARC | §11.1 | KEEP | Opt-in |
| L2ARC (SSD read-cache) | §11.3 | ATTACH | Capability-probed |
| Persistent L2ARC | §11.4 | ATTACH | Only if L2ARC is enabled |
| ARC vs OS pagecache | §11.5 | N/A | NVFS is user-space and owns its cache |
| Metaslabs | §12.1 | ADAPT | NVFS arenas ≈ metaslabs, but per-device, not per-vdev |
| ashift | §12.2 | KEEP | Already in NVFS device-probe |
| special vdev (metadata + small) | §12.3 | KEEP | Arena class "metadata" |
| dedup vdev | §12.3 | ATTACH | Only if dedup enabled |
| log vdev (SLOG) | §12.3 | KEEP | Arena class "intent-log" |
| cache vdev (L2ARC) | §12.3 | ATTACH | Arena class "read-cache" |
| Space-map log | §12.4 | KEEP | NVFS allocation-metadata is already log-structured |
| Native encryption (AES-GCM) | §13 | KEEP | Default AES-256-GCM; ChaCha20-Poly1305 option |
| Three-level key hierarchy | §13.3 | KEEP | User → wrapping → master → data keys |
| Raw encrypted send | §13.4 | KEEP | Already listed under send/recv |
| zio priority queue | §14.1 | KEEP | NVFS I/O scheduler uses it |
| TRIM / autotrim | §14.3 | KEEP | Arena-discard already exists |
| Device removal via indirect remap | §14.4 | KEEP | Pmap naturally supports it |
| `zpool import -F / -T txg` rewind | §15.1 | KEEP | Already in NVFS pmap-root history |
| `spa_load_verify` | §15.2 | KEEP | "Verify sampled pmap on import" |
| `zdb` forensic tool | §15.3 | KEEP | Ship early |
| `zpool clear` error-count reset | §15.4 | KEEP | Trivial command |
| Rollback beyond retained uberblock window | §15.5 | N/A | Same limit applies to NVFS; document it |
| Loss of non-redundant vdev | §15.5 | N/A | Same reality; document it |

**Translation highlights:**

1. **Merkle parent-stores-child checksums** are the single most load-bearing ZFS idea for NVFS. NVFS's current design puts a checksum inside each pmap entry rather than each data block; adopting the ZFS convention means widening pmap entries to 256-bit checksum + algorithm ID, and deriving the intent-log records from pmap-entry diffs. This buys end-to-end integrity at minimal cost.
2. **CoW + txg + uberblock rotation** is structurally identical to NVFS's "seal arena, publish pmap root" model, and the terminology alignment is free. Use the ZFS vocabulary (txg, uberblock, birth-txg) where it does not conflict with NVFS's existing terms.
3. **Birth-txg in the pmap entry** unlocks incremental send, snapshot dead-lists, and scrub pruning in one shot. Cheap bit to add.
4. **ARC-in-user-space** sidesteps the ZFS-on-Linux dual-cache problem entirely. NVFS owns its cache; there is no OS page cache to compete with. This is a small but real win.
5. **Allocation classes** (special / dedup / log / cache) map onto NVFS's arena classes with only a rename: "metadata arena," "dedup arena," "intent-log arena," "read-cache arena."

## 17. Open questions for NVFS design update

OQ-17.1 — **Merkle checksum placement.** Should NVFS place the per-block checksum in the pmap entry (ZFS-style, parent-stores-child) or inside the block itself (dm-integrity-style)? The ZFS approach catches misdirected writes and bus errors; the dm-integrity approach is simpler and cheaper for append-only workloads. Phase 3 decision needed.

OQ-17.2 — **Checksum algorithm default.** fletcher4 is fast but weak. blake3 is strong and fast on CPUs with SIMD; slow on embedded RISC-V. SHA-256 is universally available but slow without hardware accel. Which do we default on Simple's target architectures?

OQ-17.3 — **Ditto blocks for pmap-root.** ZFS stores up to 3 DVAs per metadata blkptr. NVFS should match — but how many arena replicas is the minimum? One (plus on-arena redundancy)? Two (mirrored pmap-roots)?

OQ-17.4 — **Replicated arenas vs device-level parity.** For an NVFS host with multiple NVMe devices, should we implement ZFS-style mirror/raid-z vdevs in the NVFS layer, or assume device-level (RAID controller, md) parity and keep NVFS single-device? Recommendation: single-device for M1, replicated-arenas for M2.

OQ-17.5 — **ARC RAM budget.** ZFS defaults to half of system RAM. For a user-space NVFS daemon, what is the appropriate RAM budget? Tied to the NVFS process's cgroup, not to total system RAM?

OQ-17.6 — **Persistent L2ARC.** Is it worth implementing, given that NVFS is already NVMe-native? Traditional L2ARC was for SATA-spinning-disk pools with a small SSD cache in front. For an all-NVMe NVFS, L2ARC is arguably pointless.

OQ-17.7 — **Dedup default.** Off, as ZFS does? Or off-with-opt-in per dataset? Per OpenZFS convention, off is correct; per-dataset opt-in via property is the right interface.

OQ-17.8 — **Dedup implementation.** Classic RAM-resident DDT or fast-dedup-style log-structured side index? Recommendation: skip dedup for M1, implement fast-dedup-style for M2.

OQ-17.9 — **Encryption default.** Off (like ZFS) or on (like ext4-fscrypt-per-directory)? "On with auto-generated key stored in kernel keyring" is ext4's direction. For NVFS, "off with easy per-dataset opt-in" matches ZFS and avoids key-management lock-in.

OQ-17.10 — **ZIL design.** Shared one ZIL per pool (ZFS) or one per arena-owning process (NVFS natural)? Recommendation: per-arena, match the rest of the NVFS arena model.

OQ-17.11 — **Send/receive stream format.** Backward-compatible with ZFS stream format (for interop) or NVFS-native? Recommendation: NVFS-native for M1, ZFS-stream importer / exporter as a Phase 5 item.

OQ-17.12 — **Scrub scheduling.** `zed`-daemon-driven (ZFS) or systemd-timer-driven (Linux distro pattern) or NVFS-internal-timer? Recommendation: expose `nvfs scrub` command; leave scheduling to the operator.

OQ-17.13 — **TRIM / discard.** Always-on autotrim by default, or off-by-default like older ZFS? Given NVFS is NVMe-native and targets recent devices, default-on autotrim is correct.

OQ-17.14 — **User-space file-backed loopback.** ZFS supports file-backed vdevs for testing. NVFS should match; this is how the test suite operates.

OQ-17.15 — **Fragmentation response.** ZFS explicitly does not defragment (CoW + snapshots make it intractable). NVFS inherits this; operators should be told to "send/receive to a fresh pool" as the fragmentation response.

OQ-17.16 — **Gang block threshold.** ZFS falls back to gang blocks when no contiguous allocation is available. NVFS should decide: tolerate gang blocks (small cost, always-available fallback) or reject the allocation and surface the fragmentation issue (admin-visible failure mode). Recommendation: tolerate, with a `nvfs_status` warning counter so operators can see the rate.

OQ-17.17 — **Embedded blkptr / tiny-file inline storage.** ZFS stores blocks ≤112 bytes inline in the blkptr. NVFS should support the same inline-in-pmap-entry path for small xattrs, small symlinks, empty-directory entries. The savings are real: a typical filesystem has millions of such entries.

OQ-17.18 — **Block cloning (reflink) as the default dedup.** OpenZFS 2.2's block cloning is already the preferred answer for most dedup scenarios. NVFS should implement block cloning before in-line dedup; likely, in-line dedup never needs to ship.

OQ-17.19 — **Checkpoint retention cost.** ZFS pool checkpoints pin all currently-allocated blocks and can balloon pool usage. NVFS should either (a) implement checkpoint with a documented "do not leave checkpoint active" warning, or (b) skip checkpoint and rely on snapshots + external backups. Lean toward (a) only if the operator feedback demands it.

OQ-17.20 — **MMP / multi-host lockout.** Does NVFS target shared-storage scenarios in M1? If yes, design MMP equivalent now. If no, defer.

## 18. Top primary sources

### 18.1 On-disk and architecture

- **OpenSolaris ZFS On-Disk Specification** (Sun Microsystems, 2006), the "On-Disk Format" paper; widely mirrored, e.g. https://open-zfs.org/wiki/Documentation/ZFSOnDiskFormat (community mirror of the original Sun PDF).
- **Jeff Bonwick and Matt Ahrens, "ZFS: The Last Word in Filesystems,"** LISA '07 talk slides.
- **Jeff Bonwick, "End-to-End Data Integrity,"** Sun blog 2005, archived https://blogs.oracle.com/bonwick/zfs-end-to-end-data-integrity.
- **Jeff Bonwick, "RAID-Z,"** Sun blog 2005, archived https://blogs.oracle.com/bonwick/raid_z.
- **Jeff Bonwick, "Smokin' Mirrors,"** Sun blog 2006 — the SSD-and-txg observation.
- **illumos manual pages:** `zpool(8)`, `zfs(8)`, `zdb(8)`, `zpoolconcepts(7)`, `zpoolprops(7)`, `zfsprops(7)`, `zpool-events(8)`.
- **FreeBSD Handbook, Chapter 22 "The Z File System (ZFS)":** https://docs.freebsd.org/en/books/handbook/zfs/.
- **OpenZFS documentation:** https://openzfs.github.io/openzfs-docs/ (canonical), Getting-Started pages, Performance-and-Tuning pages.

### 18.2 Source tree (github.com/openzfs/zfs)

- `module/zfs/spa.c`, `module/zfs/spa_history.c` — pool manager
- `module/zfs/dmu.c`, `module/zfs/dmu_tx.c`, `module/zfs/dmu_send.c`, `module/zfs/dmu_recv.c` — DMU
- `module/zfs/zil.c` — ZIL
- `module/zfs/arc.c`, `module/zfs/l2arc.c` — ARC / L2ARC
- `module/zfs/zio.c`, `module/zfs/zio_checksum.c`, `module/zfs/zio_compress.c`, `module/zfs/zio_crypt.c` — I/O pipeline
- `module/zfs/vdev.c`, `module/zfs/vdev_mirror.c`, `module/zfs/vdev_raidz.c`, `module/zfs/vdev_draid.c`, `module/zfs/vdev_label.c`, `module/zfs/vdev_queue.c`, `module/zfs/vdev_trim.c`, `module/zfs/vdev_removal.c` — vdev layer
- `module/zfs/metaslab.c`, `module/zfs/space_map.c` — allocator
- `module/zfs/ddt.c`, `module/zfs/ddt_zap.c` — dedup
- `module/zfs/dsl_dataset.c`, `module/zfs/dsl_deadlist.c`, `module/zfs/dsl_crypt.c`, `module/zfs/dsl_scan.c` — DSL (dataset + scrub)
- `module/zfs/uberblock.c`, `include/sys/uberblock_impl.h` — uberblock
- `include/sys/spa.h`, `include/sys/blkptr.h`, `include/sys/dnode.h`, `include/sys/dmu.h`, `include/sys/zil.h`, `include/sys/zio.h`, `include/sys/arc.h`, `include/sys/ddt.h`, `include/sys/vdev_impl.h`, `include/sys/metaslab_impl.h`, `include/sys/space_map.h` — headers

### 18.3 Academic and long-form

- **Bairavasundaram, Goodson, Schroeder, Arpaci-Dusseau, Arpaci-Dusseau, "An Analysis of Data Corruption in the Storage Stack,"** FAST '08. The 1.5 M disk / 41 month NetApp study.
- **Panzer-Steindel, "Data Integrity,"** CERN Internal Report, 2007.
- **Megiddo, Modha, "ARC: A Self-Tuning, Low Overhead Replacement Cache,"** FAST '03. The cache algorithm ZFS uses.
- **Plank, "A Tutorial on Reed-Solomon Coding for Fault-Tolerance in RAID-like Systems,"** Software: Practice and Experience 1997. The parity math RAID-Z uses.
- **Dominic Giampaolo, "Practical File System Design with the Be File System,"** Morgan Kaufmann 1999. The classic textbook for 64-bit-extent, attribute-indexed filesystems.
- **Rodeh, "B-trees, Shadowing, and Clones,"** ACM Transactions on Storage 2008. The general CoW-B-tree theory behind ZFS and btrfs.

### 18.4 OpenZFS Developer Summit (OZDS) proceedings

Held annually since 2013. Selected talks directly relevant to this deep dive:

- **OZDS 2013:** Matt Ahrens, "What's new in ZFS on Linux" — early OpenZFS status.
- **OZDS 2014:** Matt Ahrens, "OpenZFS: future directions."
- **OZDS 2015–2016:** Encryption design sessions by Tom Caputi (Datto).
- **OZDS 2017:** Compressed ARC; Encryption merge; lz4-in-compress-ARC.
- **OZDS 2018–2019:** Sorted scrub; dRAID; persistent L2ARC; native Linux tunables.
- **OZDS 2020:** dRAID production, OpenZFS 2.0 release review.
- **OZDS 2021:** Arc evictable-block improvements; RAID-Z expansion design.
- **OZDS 2022:** RAID-Z expansion merge; block cloning (reflinks).
- **OZDS 2023:** Fast-dedup proposal; Direct I/O.
- **OZDS 2024:** Fast-dedup merge review; RAID-Z expansion experience.

Proceedings: https://openzfs.org/wiki/OpenZFS_Developer_Summit (each year's page links slides and videos).

### 18.5 Release notes

OpenZFS release notes, github.com/openzfs/zfs "Releases" tab. Significant checkpoints:

- **0.7.0 (2017):** compressed ARC, resumable send, lz4 default.
- **0.8.0 (2019):** native encryption, sorted scrub, pool checkpoint, device removal, manual TRIM, allocation classes (special / dedup).
- **2.0.0 (2020):** zstd, persistent L2ARC, sequential resilver, redacted send.
- **2.1.0 (2021):** dRAID, InfluxDB metrics exporter.
- **2.2.0 (2023):** block cloning (reflink), BLAKE3 checksum, Linux container ID mapping.
- **2.3.0 (2024, planned/released):** fast dedup, RAID-Z expansion, direct I/O.

---

### 18.6 Selected ZFS-on-Linux / OpenZFS commits of interest

Cross-referenced by topic. The OpenZFS commit log at github.com/openzfs/zfs is the canonical record; these are the load-bearing ones for the features discussed here.

- **Native encryption** — commit `b525630` (Tom Caputi, 2017) "Native Encryption for ZFS on Linux." The merge that introduced AES-GCM and AES-CCM support.
- **Sorted scrub** — commit `d4a72f2` (Tom Caputi, 2018) "sorted scrub and resilver."
- **Resumable send** — commit `48fbb9d` (2016). Introduced resume tokens on receive side.
- **Allocation classes (special/dedup)** — commit `cc99f27` (Don Brady, 2018) "OpenZFS 9112 - Improve allocation performance on high-end storage."
- **Compressed ARC** — commit `2aa34383` (George Wilson, 2016).
- **Persistent L2ARC** — commit `77f6826b` (George Amanakis, 2020).
- **dRAID** — commit `b2255edc` (Mark Maybee + Brian Behlendorf, 2020).
- **zstd** — commit `10b3c7f` (Allan Jude + Sebastian Gottschall, 2020).
- **Block cloning** — commit `763f2fb1` (Paweł Jakub Dawidek, 2023). Added BRT and `copy_file_range()` integration.
- **BLAKE3 checksum** — commit `25311f6` (2022). Added hand-optimized BLAKE3 paths for x86_64 and aarch64.
- **Fast dedup** — merged into OpenZFS 2.3 (2024). See the `ddt_log.c` introduction commits.
- **Redacted send** — commit `30af21b0` (Paul Dagnelie, 2019).
- **Pool checkpoint** — commit `d2734ccc` (Serapheim Dimitropoulos, 2018).
- **MMP (Multi-Modifier Protection)** — commit `379ca9c` (Olaf Faaland, 2017).
- **RAID-Z expansion** — commit `1f1603c` (Don Brady + Mark Maybee, 2023).

Each commit's message references the associated design document (ZoL issue, OpenZFS proposal, or OZDS talk) which is the more verbose authoritative source for the underlying rationale.

### 18.7 Independent reviews and critiques

- **Aaron Toponce, "Install ZFS on Debian GNU/Linux"** and his ~30-part ZFS administration series, 2012. Exhaustive hands-on guide; historically the best Linux-ZFS operational reference before OpenZFS docs caught up.
- **Matt Ahrens, "OpenZFS documentation rewrite,"** OZDS 2019. The shift from the Sun-era on-disk format document to the living openzfs.github.io docs.
- **Allan Jude and Michael W. Lucas, "FreeBSD Mastery: ZFS"** and **"FreeBSD Mastery: Advanced ZFS."** IT Mastery series books, 2015–2016. FreeBSD-flavored but still the clearest operational-level guide to ZFS tuning.
- **Chris Siebenmann, "Wandering Thoughts" blog,** University of Toronto CS systems group. Decade of real-world ZFS-on-Linux operational notes, many of which are the primary source for subtle behavior (ARC sizing under Linux shrinker, L2ARC header cost in practice, etc.). https://utcc.utoronto.ca/~cks/space/blog/
- **Jim Salter, "ZFS 101,"** Ars Technica, 2020. Accessible overview; useful for cross-checking terminology but secondary to the primary sources above.

---

**End of deep dive.** This document is structured to accept diff-merge from a future Codex memo and to be cross-referenced by the next NVFS design revision. Any feature-level disputes should be resolved by cross-checking the cited primary source (OpenZFS commit, man page, OZDS slide) rather than rehashing interpretations.
