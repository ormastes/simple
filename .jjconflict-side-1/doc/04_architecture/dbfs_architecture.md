# DBFS Architecture: Database-Backed Filesystem for Simple OS

**Phase:** 3-arch | **Date:** 2026-04-28 | **Status:** LOCKED

---

## 1. Overview

DBFS is a new `FsDriver` variant for Simple OS that stores all filesystem metadata in an embedded MVCC B-tree engine and file content as page-aligned blob/extent chains. It inserts at the existing `FsDriver`/`MountTable` seam alongside `Fat32`, `Nvfs`, `NvfsPosix`, and `RamFs`. Boot and kernel images remain on FAT32; DBFS mounts at `/data` in this delivery.

---

## D1. Engine Choice: Option B — Dedicated DbFsEngine

**Decision: Option B. Fork spostgre/nvfs patterns into a dedicated `DbFsEngine`.**

Module path: `src/lib/nogc_sync_mut/db/dbfs_engine/`

**Rationale:**
- `from_spostgre.md` design notes explicitly argue against inverting the layering: spostgre sits ABOVE NVFS, consuming the `arena_*` API. DBFS is a sibling consumer of Arena+StorageClass, not a spostgre catalog extension.
- Option A (embedding spostgre as-is) would leak `Rel/BlkNo` abstractions into the filesystem layer and make the kernel-linked single-cache discipline (D9) harder to enforce — spostgre's `BufferManager` has its own clock-sweep cache keyed on `Rel/BlkNo`.
- Option B copies the structural patterns (WAL append/flush/CRC, clock-sweep buffer manager, CLRS B-tree, checkpoint ring) but defines filesystem-native key types (`Ino`, `DirEntryKey`). This adds ~500 LoC at the engine root but gives a clean separation with zero coupling to spostgre internals.
- The 8 `spostgre_if` trait contracts (`BufferManager`, `WalWriter`, `PageStore`, `PageMap`, `TempStore`, `Checkpointer`, `BlobStore`, `Vacuumer`) serve as the interface specification; `DbFsEngine` implements them with DBFS-specific type parameters.

**Reuse sources (read-only reference; no vendored changes):**
- `examples/spostgre/src/engine/wal.spl` — WAL writer with CRC32C, group-commit, arena-backed log
- `examples/spostgre/src/engine/buffer_mgr.spl` — clock-sweep buffer manager
- `examples/spostgre/src/engine/checkpoint.spl` — checkpoint sealing protocol
- `examples/nvfs/src/core/pmap_btree.spl` — full CLRS B-tree (delete/rebalance), key type generalized
- `examples/nvfs/src/core/intent_log.spl` — intent log structure (must add disk persistence)
- `examples/nvfs/src/core/checkpoint.spl` — 4096-slot ring (must add META_DURABLE persistence)
- `src/lib/nogc_sync_mut/spostgre_if/` — 8 trait contract definitions

---

## D2. Gap List Against Chosen Engine

Six gaps must be closed for AC-3. Each has a design, module path, and LoC budget.

### Gap 1: DBFS Catalog Schema (11 table types, page-structured)

**Design:** Define 11 page-structured relation types in `dbfs_schema.spl`. Each table maps to a contiguous arena region. Page size: 8 KiB. Pages contain a 16-byte header (`magic: u32`, `page_type: u8`, `gen: u64`, `checksum: u32`) followed by fixed-width rows (for INODE/DENTRY) or variable-width entries (for WAL_RECORD/XATTR). B-tree internal nodes hold `(key, child_page_id)` pairs; leaf nodes hold `(key, row_data)` pairs. See D3 for full schema.

**Module:** `src/lib/nogc_sync_mut/db/dbfs_engine/schema.spl`
**LoC budget:** ~200

### Gap 2: Namespace B-tree with Ino/DirEntryKey

**Design:** Structural copy of `examples/nvfs/src/core/pmap_btree.spl` with key type changed from `(arena_id: i64, offset: i64)` to `DentryKey { parent_ino: i64, name_hash: i64 }` for DENTRY lookup and `InodeKey { ino: i64 }` for INODE lookup. The B-tree is generic over a key trait `BTreeKey` with `cmp()` and `encode_page()` methods. Delete uses the same CLRS top-down rebalancing. No other structural changes.

**Module:** `src/lib/nogc_sync_mut/db/dbfs_engine/ns_btree.spl`
**LoC budget:** ~350 (pmap_btree is ~300; +50 for key generalization)

### Gap 3: RawNvmeArena — Arena over BlockDevice

**Design:** A new struct `RawNvmeArena` implements the `Arena` trait by translating arena verbs to raw NVMe `read_sector`/`write_sector` calls. Arena handles map to LBA ranges. `arena_create(class, hint_bytes)` allocates an LBA range from a simple bump allocator in the superblock. `arena_append(h, data, durability)` writes sectors; DURABLE_GROUP_COMMIT level calls `write_sector` + issues a flush command. `arena_readv(h, off, buf)` reads sectors. `arena_seal(h, gen)` writes a seal record at the LBA-range footer. `arena_discard(h)` marks the range as free in the superblock bitmap.

**Module:** `src/lib/nogc_sync_mut/db/dbfs_engine/raw_nvme_arena.spl`
**LoC budget:** ~250

### Gap 4: Intent Log Disk Persistence

**Design:** The current `examples/nvfs/src/core/intent_log.spl` holds records in an in-memory `Vec`. DBFS's `DbFsIntentLog` writes each appended record to the `DB_WAL` arena via `arena_append(wal_handle, record_bytes, DURABLE_GROUP_COMMIT)` before returning. The in-memory buffer is retained as a read cache (replay scan uses the on-disk log). On mount, the intent log is reconstructed by reading the `DB_WAL` arena from `intent_log_head` LSN forward. The log is a linear sequence of fixed-header + variable-payload records. Log rotation happens at checkpoint: the old WAL arena is sealed; a new `DB_WAL` arena is created; `intent_log_head` in the checkpoint entry points to the new arena's start.

**Module:** `src/lib/nogc_sync_mut/db/dbfs_engine/intent_log.spl`
**LoC budget:** ~200

### Gap 5: Checkpoint Ring Disk Persistence

**Design:** The current `examples/nvfs/src/core/checkpoint.spl` maintains 4096 slots in memory. DBFS's `DbFsCheckpointRing` writes each `CheckpointEntry` to the `META_DURABLE` arena via `arena_append` after all sealed arenas are confirmed durable. A `CheckpointEntry` contains: `gen: u64`, `clean: bool`, `intent_log_head: Lsn`, `root_ino_page: PageId`, `wall_time: i64`, `checksum: u32`. The ring is a circular log in the META_DURABLE arena; the latest entry with `clean=true` is the recovery starting point. On mount, the ring is scanned from the end backward to find the last clean entry.

**Module:** `src/lib/nogc_sync_mut/db/dbfs_engine/checkpoint_ring.spl`
**LoC budget:** ~150

### Gap 6: Power-Cut Simulation Harness

**Design:** A test harness that wraps `Arena` and injects a configurable fault after N write calls. The fault causes all subsequent `arena_append` calls to return `Err(IoError::SimulatedPowerCut)`. The test then creates a fresh `DbFsEngine` from the same (partially-written) backend and runs mount recovery. Assertions: (a) all committed transactions are visible, (b) uncommitted transactions are absent, (c) no orphaned extents remain referenced. This is an interpreter-mode-only spec (per `feedback_compile_mode_false_greens`).

**Module:** `test/dbfs/power_cut_harness.spl`
**LoC budget:** ~180

---

## D3. On-Disk Schema

All tables are page-structured with 8 KiB pages. B-tree keys are listed as `(key_cols...)` sorted lexicographically. "Region" = the `StorageClass` arena where pages live.

### INODE
| Column | Type | Notes |
|--------|------|-------|
| ino_id | i64 PK | Auto-increment; 0 = root |
| gen | u64 | Mutation generation |
| mode | u32 | Unix permission bits |
| uid | u32 | Owner UID |
| gid | u32 | Owner GID |
| link_count | u32 | Hard links (always 1 for this delivery) |
| size | u64 | Logical file size in bytes |
| mtime | i64 | Modification time (ns since epoch) |
| ctime | i64 | Change time (ns since epoch) |
| flags | u32 | DBFS-specific flags (snapshot, immutable, …) |

**B-tree key:** `(ino_id)` — 8 bytes. Leaf row: 64 bytes. Pages hold ~120 rows.
**Region:** `META_DURABLE`. **Page budget:** 64 KiB for 1M inodes (8192 pages × 120 rows).

### DENTRY
| Column | Type | Notes |
|--------|------|-------|
| parent_ino | i64 PK | |
| name | text(255) | UTF-8 filename |
| child_ino | i64 | |
| gen | u64 | Child generation at link time |

**B-tree key:** `(parent_ino, name_hash: i64)` — 16 bytes. Collision chain in leaf.
**Region:** `META_DURABLE`. **Page budget:** 128 KiB for 100K entries.

### FILE_VERSION
| Column | Type | Notes |
|--------|------|-------|
| ino_id | i64 PK | |
| gen | u64 PK | |
| root_extent_ref | i64 | FK → EXTENT_REF.ino_id |
| version_flags | u32 | snapshot/fork bits |

**B-tree key:** `(ino_id, gen)` — 16 bytes.
**Region:** `META_DURABLE`. **Page budget:** 16 KiB.

### EXTENT_REF
| Column | Type | Notes |
|--------|------|-------|
| ino_id | i64 PK | |
| gen | u64 PK | |
| logical_offset | u64 PK | Byte offset in file |
| length | u64 | Byte length of this extent |
| extent_id | i64 | FK → EXTENT |

**B-tree key:** `(ino_id, gen, logical_offset)` — 24 bytes.
**Region:** `META_DURABLE`. **Page budget:** 32 KiB for 10K extents.

### EXTENT
| Column | Type | Notes |
|--------|------|-------|
| extent_id | i64 PK | Auto-increment |
| blob_id | i64 | FK → BLOCK_BLOB |
| offset_in_blob | u64 | Byte offset within blob |
| length | u64 | Byte length |
| checksum | u32 | CRC32C of content |
| compression | u8 | 0=none, 1=lz4, 2=zstd |
| birth_gen | u64 | Generation when created |
| storage_class | u8 | FK → STORAGE_CLASS.class_id |

**B-tree key:** `(extent_id)` — 8 bytes.
**Region:** `META_DURABLE`. **Page budget:** 16 KiB.

### BLOCK_BLOB
| Column | Type | Notes |
|--------|------|-------|
| blob_id | i64 PK | |
| backend | u8 | 0=raw_nvme, 1=nvfs_arena |
| backend_addr | u64 | LBA or arena handle |
| length | u64 | Blob byte length |

**B-tree key:** `(blob_id)` — 8 bytes.
**Region:** `META_DURABLE`. **Page budget:** 8 KiB.

### XATTR
| Column | Type | Notes |
|--------|------|-------|
| ino_id | i64 PK | |
| name | text(255) PK | |
| value | bytes(65535) | |

**B-tree key:** `(ino_id, name_hash)` — 16 bytes. Variable-length value in leaf overflow pages.
**Region:** `META_DURABLE`. **Page budget:** 8 KiB + overflow.

### ACL_ENTRY
| Column | Type | Notes |
|--------|------|-------|
| ino_id | i64 PK | |
| principal | u64 PK | UID/GID packed |
| perms | u32 | rwxrwxrwx bits |
| allow_deny | u8 | 0=allow, 1=deny |

**B-tree key:** `(ino_id, principal)` — 16 bytes.
**Region:** `META_DURABLE`. **Page budget:** 8 KiB.

### TXN
| Column | Type | Notes |
|--------|------|-------|
| txn_id | i64 PK | xmin in MVCC terms |
| status | u8 | 0=in-progress, 1=committed, 2=aborted |
| lsn_first | u64 | First WAL LSN of this txn |
| lsn_last | u64 | Last WAL LSN (set at commit) |

**B-tree key:** `(txn_id)` — 8 bytes.
**Region:** `DB_WAL`. **Page budget:** 8 KiB.

### WAL_RECORD
| Column | Type | Notes |
|--------|------|-------|
| lsn | u64 PK | Monotonic log sequence number |
| txn_id | i64 | FK → TXN |
| record_type | u8 | INSERT/UPDATE/DELETE/COMMIT/ABORT |
| payload | bytes | Serialized row delta |

**Layout:** Fixed 24-byte header + variable payload. Records are appended sequentially; no B-tree index.
**Region:** `DB_WAL`. **Page budget:** 64 KiB per WAL rotation window.

### STORAGE_CLASS
| Column | Type | Notes |
|--------|------|-------|
| class_id | u8 PK | 0=META_DURABLE … 5=CHECKPOINT_SNAPSHOT |
| backend_kind | u8 | 0=raw_nvme, 1=nvfs_arena |
| hints | u64 | Backend-specific hints (stripe width, etc.) |

**B-tree key:** `(class_id)` — 1 byte. Static table; 6 rows.
**Region:** `META_DURABLE`. **Page budget:** 1 KiB.

---

## D4. Transaction Write Protocol

**Group-commit window:** None for v1. Each write transaction commits individually. Adding group-commit is a follow-up optimization.

**Concurrency model (pessimistic write locking — chosen for v1 simplicity):**
Writers hold the inode write lock (RwLock, exclusive) for the full duration of steps 1–5. Because only one writer holds the inode lock at a time, CAS contention on a single inode's B-tree root pointer cannot occur — the CAS at step 5 is therefore always a formality (current root == snapshot root is guaranteed). Optimistic generation checks at D8 apply to **readers** detecting a concurrent committed write (they re-read if `Inode.gen` changed between snapshot and use), not to the writer path. Phase 5 must implement this discipline: writer holds RwLock write mode; readers hold RwLock read mode and re-validate gen after each page read. No optimistic-retry loop is needed in the writer path.

**WAL record structure:** One transaction produces N row-mutation WAL_RECORDs (record_type ∈ INSERT/UPDATE/DELETE, one per modified row) followed by exactly one COMMIT WAL_RECORD. The single DURABLE_GROUP_COMMIT flush at step 4 covers the entire batch including the COMMIT record. Recovery identifies a committed transaction by finding its COMMIT record in the WAL; all row-mutation records without a following COMMIT are discarded.

**6-step write path:**

1. **Write data blobs/extents.** Acquire inode write lock (RwLock exclusive). Allocate a new `blob_id` and arena handle via `arena_create(GENERAL_MUTABLE, size_hint)`. Write file content pages via `arena_append(blob_handle, page_data, ASYNC)`. Update `EXTENT` and `BLOCK_BLOB` rows in private (not yet published) buffer pages.

2. **Build new metadata in private pages.** Copy-on-write: load the affected INODE, DENTRY, EXTENT_REF pages into a private buffer (dirty bit set). Apply row mutations. Mark pages as dirty. Do NOT publish the B-tree root pointer yet. The writer holds the inode write lock from step 1 through step 5; no concurrent writer can intervene.

3. **Append WAL row-mutation records.** For each modified row: serialize a `WAL_RECORD{record_type: INSERT|UPDATE|DELETE, txn_id, payload: row_delta}`. Assign monotonically increasing LSNs. Buffer these in the intent log's in-memory write buffer. Do NOT flush yet.

4. **Append COMMIT record and flush WAL to durable storage.** Append a final `WAL_RECORD{record_type: COMMIT, txn_id, lsn_last: current_lsn}` to the buffer. Call `DbFsIntentLog.flush()` which calls `arena_append(wal_handle, all_buffered_records, DURABLE_GROUP_COMMIT)`. Returns only after WAL bytes are confirmed on stable storage. The transaction is "committed on paper" — it will survive a crash from this point.

5. **Publish new root atomically.** Update the in-memory B-tree root page pointer to the new COW root. Because the inode write lock is held, this is a simple store (no CAS needed). Update `TXN.status = committed` and `TXN.lsn_last` in the in-memory TXN table.

6. **Make visible.** Release the inode write lock. Subsequent readers will see the new `Inode.gen` value and read from the updated B-tree root. Readers that began a snapshot before step 6 continue to see the old gen (MVCC isolation).

**fsync points:** Only one: step 4 (`DURABLE_GROUP_COMMIT` flush covering all N row-mutation records + COMMIT record). No additional fsync at publish. The WAL is the durability anchor.

---

## D5. Recovery Model

### Mount-time procedure (5 steps):

**Step 1 — Superblock probe.** Read superblock LBA (fixed offset 0 on the device). If the primary superblock fails CRC, try replica at offset 1 (1-block offset) and 2 (end-of-device minus 1 block). Use the replica with the highest `gen` field and valid CRC. If all three fail, mount fails with `EIO`.

**Step 2 — Checkpoint ring scan.** Open the `META_DURABLE` arena via the superblock's `meta_durable_lba`. Scan `CheckpointEntry` records from newest to oldest. Find the latest entry with `clean=true`. If none found (first mount or total corruption), initialize empty DBFS structures.

**Step 3 — WAL replay.** Open the `DB_WAL` arena. Read WAL records starting from `checkpoint_entry.intent_log_head` LSN. For each record:
- If `record_type == COMMIT` and `TXN.status` in the WAL confirms committed: apply the row delta to the B-tree pages in memory.
- If `record_type == ABORT` or the txn has no matching COMMIT record before the WAL tail: skip (treat as uncommitted).
- Never replay WAL records whose LSN is before `intent_log_head`.

**Step 4 — Orphan reclamation.** Enumerate all arena handles created after the last clean checkpoint generation. For each arena not referenced by any EXTENT or BLOCK_BLOB row in the recovered B-tree: call `arena_discard(handle)`. `arena_discard` is idempotent; safe to call on already-discarded arenas.

**Step 5 — Clean mount generation publication.** Write a new `CheckpointEntry` with `clean=true`, `gen = last_clean_gen + 1`, `intent_log_head = current_wal_head`. This establishes the post-recovery clean baseline. Future power cuts will replay from this point, not the pre-crash checkpoint.

**Committed vs. uncommitted decision rule:** A transaction is committed if and only if a WAL_RECORD with `record_type == COMMIT` for its `txn_id` appears in the WAL at or before the WAL tail LSN. All other transactions are uncommitted regardless of partial row deltas.

---

## D6. BlobBackend Trait Shape

**Decision: No new trait needed. The existing `Arena` trait at `src/lib/nogc_sync_mut/storage/arena.spl` IS the BlobBackend.**

Locked file path: `src/lib/nogc_sync_mut/storage/arena.spl`

7-verb API (locked, no changes to this file):
```
arena_create(class: StorageClass, hint_bytes: u64) -> Result<ArenaHandle>
arena_append(h: ArenaHandle, data: [u8], durability: DurabilityLevel) -> Result<u64>  // returns offset
arena_readv(h: ArenaHandle, off: u64, buf: mut [u8]) -> Result<()>
arena_seal(h: ArenaHandle, gen: u64) -> Result<()>
arena_discard(h: ArenaHandle) -> Result<()>
arena_clone_range(src: ArenaHandle, src_off: u64, dst: ArenaHandle, dst_off: u64, len: u64) -> Result<()>
arena_preferred_granule(h: ArenaHandle) -> u64
```

**Raw NVMe backend implementation (`RawNvmeArena`):**
- `arena_create` → allocate LBA range from superblock bump allocator; return handle encoding (start_lba, length_sectors)
- `arena_append` → `BlockDevice.write_sector(lba, data)` in sector-aligned chunks; DURABLE_GROUP_COMMIT issues NVMe Flush command after writes
- `arena_readv` → `BlockDevice.read_sector(lba, buf)` in sector-aligned chunks
- `arena_seal` → write a 1-sector seal record at (start_lba + allocated_sectors - 1) with gen and CRC
- `arena_discard` → clear the LBA range entry in the superblock bitmap; write updated superblock
- `arena_clone_range` → read-modify-write at the sector level
- `arena_preferred_granule` → `BlockDevice.sector_size()` (typically 512 or 4096)

**NVFS-arena backend implementation:** Existing concrete NVFS Arena impl in `examples/nvfs/src/core/arena.spl` already satisfies the trait. No changes needed to existing NVFS consumers.

**DbFsDriver constructor signature:**
```
fn new<B: Arena>(backend: B, opts: DbFsMountOpts) -> Result<DbFsDriver<B>>
```
The generic parameter `B` is erased at the DriverInstance variant level by boxing or concrete instantiation per mount call.

---

## D7. FsDriver Seam Edits

Six files require changes. The compiler's exhaustive-match enforcement will surface every unhandled site as a compile error when `DbFs` is added.

| # | File | Change |
|---|------|--------|
| 1 | `src/lib/nogc_sync_mut/fs_driver/instance.spl` | Add `DbFs(driver: DbFsDriver)` to `enum DriverInstance`; add `DbFs(d) => "dbfs"` arm in `driver_name()` |
| 2 | `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` | Add `DbFs` arms in any exhaustive match on `DriverInstance` |
| 3 | `src/lib/nogc_sync_mut/fs_driver/ops.spl` | Dispatch arms (if match exists); verify docstring dispatch examples include DbFs |
| 4 | `src/lib/nogc_sync_mut/fs_driver/__init__.spl` | Export `DbFsDriver` and `DbFsMountOpts` |
| 5 | `src/lib/nogc_sync_mut/driver/core.spl` | Add `DbFs` arms in any match on `DriverInstance` |
| 6 | `src/os/services/vfs/vfs_init.spl` | Add DBFS mount for `/data` path; construct `DbFsDriver` with appropriate backend |

**New file (not a seam edit):**
- `src/lib/nogc_sync_mut/fs_driver/dbfs_stub.spl` — `DbFsDriver` struct implementing `FsDriver` trait (analogous to `ramfs.spl`)

**Capability set DBFS reports:**
```
capabilities() -> [COW, Xattr, Acl, LargeFiles, PosixCompat]
```
Extension probe:
```
probe(PosixCompatExt) -> Some(DbFsPosixCompatExt { ... })
probe(XattrExt)       -> Some(DbFsXattrExt { ... })
probe(AclExt)         -> Some(DbFsAclExt { ... })
probe(SnapshotExt)    -> Some(DbFsSnapshotExt { ... })
probe(_)              -> None
```
No new `Capability` enum variants needed — all 4 are already in the existing enum.

---

## D8. Locking Layers

### Lock primitives (all from existing repo `src/lib/nogc_sync_mut/sync/`):
- `Mutex<T>` — exclusive lock (used for mount lock, directory lock)
- `RwLock<T>` — reader-writer lock (used for inode data lock; writers hold exclusive; readers hold shared)
- `SpinLatch` — page latch for buffer manager (existing in spostgre buffer_mgr pattern)
- Reader gen-revalidation — readers compare `Inode.gen` at snapshot time vs. after each page read; if changed, re-read from updated root (no retry for writers — writer holds RwLock exclusive, so gen cannot change under it)

### Lock hierarchy (must always acquire in this order to prevent deadlock):

1. **Mount lock** (`Mutex`) — held during mount/unmount only; not held during normal I/O
2. **Directory lock** (`Mutex`) — per-directory; held during namespace mutations (mkdir, unlink, rename)
3. **Inode RW lock** (`RwLock`) — per-inode; readers share; writers exclusive during write path steps 1-5
4. **Page latch** (`SpinLatch`) — per-buffer-page; held only during page read/write in buffer manager (microseconds)
5. **Optimistic gen check** — at commit (step 5), verify `Inode.gen` unchanged; if changed, drop all locks and retry from step 2

### Rename two-parent rule:
Lock both parent directories in **ascending inode-id order** to prevent deadlock. Pseudocode:
```
if src_parent_ino < dst_parent_ino:
    lock(src_parent_dir), then lock(dst_parent_dir)
else if src_parent_ino > dst_parent_ino:
    lock(dst_parent_dir), then lock(src_parent_dir)
else:
    lock(src_parent_dir)   // same directory; one lock
```

---

## D9. Kernel-Linked vs. Hosted Build

### Build flag: `dbfs_kernel_linked`

**Conditional compilation strategy in Simple:**
```simple
#[cfg(dbfs_kernel_linked)]
fn create_buffer_manager() -> DbFsBufferManager {
    // Kernel build: use a single fixed-size page pool; no GC runtime
    DbFsBufferManager::new_fixed(KERNEL_DBFS_CACHE_PAGES)
}

#[cfg(not(dbfs_kernel_linked))]
fn create_buffer_manager() -> DbFsBufferManager {
    // Hosted build: use configurable cache size from mount opts
    DbFsBufferManager::new_dynamic(opts.cache_pages)
}
```

**Single-cache discipline enforcement:**
- When `dbfs_kernel_linked` is set, the kernel page cache (`src/os/kernel/mm/`) must NOT also cache DBFS metadata pages. Enforced by convention: DBFS buffer manager owns pages identified by `(ino_id, page_id)` tuples; the kernel page cache owns pages by `(device_id, lba)` tuples. DBFS metadata pages are never inserted into the kernel page cache. This is verified in the Phase 7 spec by checking that metadata I/O bypasses the kernel `page_cache_insert` call path.
- `DbFsBufferManager` in kernel build: fixed 512-page pool (configurable at compile time via `KERNEL_DBFS_CACHE_PAGES` constant). No dynamic allocation after init.
- `DbFsBufferManager` in hosted build: dynamic allocation via `nogc_sync_mut` allocator; cache size from `DbFsMountOpts.cache_pages`.

**Scope:** Stage 2 (kernel-linked) is in scope. The flag gates only the buffer manager construction and the allocator backend. All other DBFS code compiles identically in both configurations.

---

## D10. POSIX-Compat Shim Subset

**Mirror NvfsPosix discipline.** DBFS exposes a `PosixCompatExt` extension.

### Supported ops (in scope for this delivery):

| Op | Implementation |
|----|----------------|
| `open(path, O_RDWR)` | MVCC snapshot read + inode write lock |
| `read(fd, buf, len)` | Extent lookup via EXTENT_REF B-tree + blob read |
| `write(fd, buf, len)` | COW: allocate new EXTENT + BLOCK_BLOB; update EXTENT_REF; 6-step write path |
| `pread` / `pwrite` | Same as read/write with explicit offset |
| `stat(path)` / `fstat(fd)` | INODE lookup (read-only, no lock) |
| `readdir(path)` | DENTRY B-tree range scan on `parent_ino` |
| `mkdir(path, mode)` | New INODE + DENTRY insert; 6-step write path |
| `unlink(path)` | Tombstone DENTRY; decrement `link_count`; if 0, queue for vacuum |
| `rename(src, dst)` | Lock both parents (D8 order); update DENTRY atomically; COW INODE gen bump |
| `truncate(path, len)` | COW: remove/trim EXTENT_REFs beyond `len`; update INODE.size |
| `symlink(target, path)` | INODE with `mode=S_IFLNK`; store target in XATTR `symlink.target` |
| `readlink(path)` | Read `symlink.target` XATTR |
| `setxattr` / `getxattr` | XATTR B-tree insert/lookup |
| `getfacl` / `setfacl` | ACL_ENTRY B-tree insert/lookup |

### Random write via COW path:
`pwrite(fd, buf, offset, len)` → allocate new `blob_id` for the written range → insert/update `EXTENT_REF(ino_id, gen+1, logical_offset)` pointing to new extent → old EXTENT_REF for overlapping range is deleted (or trimmed) → new `gen` is published atomically.

### Explicitly out of scope (document for AC-10):

| Op | Reason out of scope |
|----|---------------------|
| `mmap(MAP_SHARED + PROT_WRITE)` | Requires kernel VM integration; deferred |
| Hard links (`link()`) | `link_count > 1` not tracked in this delivery |
| Sparse file holes (`fallocate PUNCH_HOLE`) | Hole-punch in EXTENT_REF deferred |
| `O_DIRECT` | Bypasses buffer manager; deferred |
| `fsync` per-file | Not exposed; WAL provides per-txn durability |
| `flock` / `fcntl` advisory locks | Deferred |

---

## D11. Test/Benchmark Plan Handoff to Phase 4

All specs are interpreter-mode only (per `feedback_compile_mode_false_greens`). No `--mode=native` or `--mode=smf`.

### Spec files Phase 4 must write:

| Spec file | Covers |
|-----------|--------|
| `test/dbfs/engine/pager_spec.spl` | Buffer manager: page eviction, dirty tracking, clock-sweep |
| `test/dbfs/engine/btree_spec.spl` | Namespace B-tree: insert/lookup/delete/range-scan with Ino/DirEntryKey |
| `test/dbfs/engine/wal_spec.spl` | WAL: append, flush, LSN monotonicity, CRC32C correctness |
| `test/dbfs/engine/recovery_spec.spl` | Mount recovery: clean mount, crash-then-recover, orphan reclaim |
| `test/dbfs/driver/dbfs_driver_spec.spl` | FsDriver trait: mount, open, read, write, stat, readdir, mkdir, unlink, rename |
| `test/dbfs/driver/capability_spec.spl` | Extension probe: COW/Xattr/Acl/LargeFiles/PosixCompat reported correctly |
| `test/dbfs/driver/nvfs_arena_backend_spec.spl` | NVFS-arena-as-backend: DbFsDriver with NVFS Arena impl (AC-4) |
| `test/dbfs/driver/raw_nvme_backend_spec.spl` | RawNvmeArena: sector reads/writes, arena verbs on BlockDevice mock |
| `test/dbfs/integration/fat32_nonregression_spec.spl` | FAT32 still mounts, reads dirs, opens files after DBFS code lands (AC-7) |
| `test/dbfs/integration/mount_table_dispatch_spec.spl` | MountTable dispatches to DbFs variant; exhaustive match compiles |
| `test/dbfs/power_cut_harness.spl` | Power-cut simulation: committed txns survive, uncommitted absent (AC-5) |
| `test/dbfs/bench/metadata_storm_bench.spl` | Benchmark: 10K mkdir/stat ops; baseline latency recorded |
| `test/dbfs/bench/append_log_bench.spl` | Benchmark: append-heavy log file; throughput MB/s |
| `test/dbfs/bench/random_overwrite_bench.spl` | Benchmark: random 4K writes on 1 GiB file; IOPS |
| `test/dbfs/bench/mmap_read_bench.spl` | Benchmark: sequential read via readv; throughput |

---

## D12. Risk Register

| # | Risk | Severity | Mitigation |
|---|------|----------|------------|
| R1 | Intent log persistence gap (HIGH) | HIGH | Gap 4 is a required deliverable; must flush to DB_WAL arena before returning from wal_append; spec in wal_spec.spl verifies durable return |
| R2 | Checkpoint ring persistence gap (HIGH) | HIGH | Gap 5 is a required deliverable; CheckpointEntry written to META_DURABLE before clean=true; spec in recovery_spec.spl verifies post-crash ring scan |
| R3 | Double journaling (DBFS WAL + NVMe FTL) | MEDIUM | Use DURABLE_GROUP_COMMIT (one flush per commit, not per record); document explicitly in AC-10 doc; no per-record fsync |
| R4 | Double cache (DBFS buffer manager + kernel page cache) | MEDIUM | Single-cache discipline: DBFS pages keyed by (ino_id, page_id); kernel cache keyed by (device_id, lba); never cross-insert; verified in Phase 7 |
| R5 | Large-file random overwrite COW amplification | MEDIUM | Random write rewrites one EXTENT_REF per 4K write (worst case); mitigated by extent coalescing in vacuum pass; benchmarked in random_overwrite_bench.spl |
| R6 | Namespace B-tree key generalization mismatch | MEDIUM | pmap_btree structural copy with DentryKey; btree_spec.spl ports all 3 original tests to new key type; no runtime behavior change |
| R7 | Power-cut harness complexity (AC-5) | MEDIUM | Harness wraps Arena with fault injection (N-write threshold); simpler than real device testing; interpreter-mode only |
| R8 | spostgre_if Rel/BlkNo coupling leak | MEDIUM | DbFsEngine defines own Ino/DirEntryKey; never imports spostgre type definitions; enforced by no cross-module import of spostgre types |
| R9 | Recovery bugs in orphan reclamation | MEDIUM | arena_discard is idempotent; worst case: disk space not reclaimed, not data corruption; recovery_spec verifies no false-positive discards |
| R10 | jj submodule gitlink flip during parallel work | LOW | Per memory note: accept gitlinks-as-tree; commit per-phase immediately; no parallel /dev tracks during DBFS phase work |
| R11 | Stage 2 rt_* extern bootstrap rebuild | LOW | Any new rt_* extern requires full bootstrap (scripts/bootstrap/bootstrap-from-scratch.sh --deploy); documented in implementation handoff |
| R12 | Scope creep (distributed NVFS, xfstests, mmap shared-write) | LOW | Explicitly out of scope per Phase 1 decisions; out-of-scope list locked in D10 |
| R13 | Submodule race with parallel /dev auto-snapshot | LOW | Per memory `feedback_submodule_race_parallel_dev`: jj auto-snapshot between stage and commit converts gitlinks to 040000 tree. Mitigation: pause all parallel sstack/dev tracks before starting DBFS phase work; resume only after each atomic commit lands. Commit per-phase immediately (per `feedback_sync_bundling_clobbers_commits`). |

---

## Module Map Summary

### New modules (all under `src/lib/nogc_sync_mut/db/dbfs_engine/`):

| File | Purpose | LoC budget |
|------|---------|-----------|
| `__init__.spl` | Module root; exports | 30 |
| `engine.spl` | `DbFsEngine` struct composing 8 traits | 200 |
| `schema.spl` | 11 catalog types, page header, row serializers | 200 |
| `ns_btree.spl` | B-tree with `Ino`/`DirEntryKey` key types | 350 |
| `intent_log.spl` | WAL intent log with disk persistence | 200 |
| `checkpoint_ring.spl` | Checkpoint ring with META_DURABLE persistence | 150 |
| `raw_nvme_arena.spl` | `RawNvmeArena: Arena` over `BlockDevice` | 250 |
| `buffer_mgr.spl` | Clock-sweep buffer manager (Ino/BlkNo keyed) | 300 |
| `txn.spl` | Transaction context, MVCC xmin/xmax | 150 |
| `recovery.spl` | Mount-time 5-step recovery procedure | 200 |

### New FsDriver stub:
- `src/lib/nogc_sync_mut/fs_driver/dbfs_stub.spl` — `DbFsDriver` implementing `FsDriver` trait (~400 LoC)

### Modified files (seam edits, D7):
- `src/lib/nogc_sync_mut/fs_driver/instance.spl` — add variant
- `src/lib/nogc_sync_mut/fs_driver/mount_table.spl` — add arms
- `src/lib/nogc_sync_mut/fs_driver/ops.spl` — add arms if match exists
- `src/lib/nogc_sync_mut/fs_driver/__init__.spl` — add exports
- `src/lib/nogc_sync_mut/driver/core.spl` — add arms
- `src/os/services/vfs/vfs_init.spl` — add DBFS mount for `/data`

### Test files (Phase 4 writes these, not Phase 5):
- 15 spec files under `test/dbfs/` as listed in D11

**Total new LoC estimate:** ~2,230 (engine + stub) + ~1,800 (tests) = ~4,030

---

## Staged Rollout

| Stage | Config | Deliverable |
|-------|--------|------------|
| Stage 1 | Hosted (default build) | DBFS mounts on `/data` in hosted test environment; all specs pass interpreter-mode |
| Stage 2 | `dbfs_kernel_linked` flag | DBFS buffer manager uses fixed pool; mounts in kernel build; single-cache verified |
| Stage 3 | Arena specialization (deferred) | NVFS arena backend optimization; not in this delivery |

---

*End of DBFS Architecture. Phase 4 (Spec) reads this document to write spec files.*
