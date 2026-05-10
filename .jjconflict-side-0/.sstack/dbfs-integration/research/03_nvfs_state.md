# Stream C — NVFS Current State

**Date:** 2026-04-28

## NVFS File Inventory

**Trait contracts** (`src/lib/nogc_sync_mut/fs/nvfs/`):
- `api.spl` — re-exports `Arena`, `ArenaHandle`, `ArenaAppendResult` from `std.storage.arena`
- `extent_map.spl` — `ExtentMapEntry` struct + `ExtentMap` trait (lookup/insert/truncate/total_length)
- `superblock_if.spl` — `SuperblockHeader` struct + `SuperblockReader` trait (read_header/is_mounted/last_checkpoint_generation)
- `__init__.spl` — module docstring; note: "spostgre and other storage consumers need the SAME Arena trait"

**POSIX shim** (`src/lib/nogc_sync_mut/fs/nvfs_posix/`):
- `cow_engine.spl` — `CowShadow` struct + `CowShadowOps` trait (new/splice/commit)
- `api.spl` — `FdId` + `NvfsPosixOps` supplemental trait

**Concrete impls** (`examples/nvfs/src/core/`):
- `arena.spl` — concrete Arena impl
- `checkpoint.spl` — checkpoint ring (4096 slots, in-memory, structure ready for disk)
- `intent_log.spl` — in-memory append-only WAL (no disk I/O)
- `pmap_btree.spl` — full B-tree (insert/lookup/delete, CLRS top-down, rebalancing)
- `pmap.spl` — page-indirection map
- `superblock.spl` — superblock reader/writer
- `extent.spl` — extent chain management
- `ns_tree.spl` — namespace tree
- `reflink.spl`, `dedup.spl`, `scrub.spl`, `compression.spl`, `encryption.spl`, `send.spl` — capability impls

## Subsystem Persistence Status

| Subsystem | Status | Notes |
|---|---|---|
| Arena (arena_create/append/seal/discard/clone_range) | In-memory placeholder → real in concrete impl | examples/nvfs/src/core/arena.spl is concrete |
| Namespace (ns_tree) | In-memory | No disk persistence yet |
| ExtentMap (logical→physical) | Trait only in main repo; concrete in examples/nvfs | examples/nvfs/src/core/extent.spl |
| Intent log (WAL-like) | **In-memory only** (no disk I/O, per source comment) | N1 milestone, disk persistence = gap |
| Superblock | Trait in main repo; concrete in examples/nvfs | examples/nvfs/src/core/superblock.spl |
| Checkpoint ring | **In-memory, 4096 slots** | No disk write yet; structure ready |
| pmap B-tree | **Full in-memory B-tree** | examples/nvfs/src/core/pmap_btree.spl |
| Reflink/dedup/scrub/compress/encrypt | Concrete stubs in examples/nvfs | Status varies |

## StorageClass Enum (already defined)

**File:** `src/lib/nogc_sync_mut/storage/storage_class.spl`

6 classes: `META_DURABLE, DB_WAL, DB_TEMP, MODEL_IMMUTABLE, GENERAL_MUTABLE, CHECKPOINT_SNAPSHOT`

DBFS needs all 6; no new StorageClass values needed.

## Arena Trait (BlobBackend seam)

**File:** `src/lib/nogc_sync_mut/storage/arena.spl`

7 verbs: `arena_create(class, hint_bytes)`, `arena_append(h, data, durability)`, `arena_readv(h, off, buf)`, `arena_seal(h, gen)`, `arena_discard(h)`, `arena_clone_range(src, src_off, dst, dst_off, len)`, `arena_preferred_granule(h)`

**This IS the BlobBackend trait.** The design doc's `BlobBackend` concept maps exactly to the existing `Arena` trait. DBFS extents should target this trait. Both raw-NVMe and NVFS-arena backends can implement `Arena`, giving DBFS the pluggable backend (AC-4) without a new trait.

## NVFS BlobBackend Refactor Seam

**What already exists:** `Arena` trait in `src/lib/nogc_sync_mut/storage/arena.spl` — this is the exact seam. Current NVFS driver holds the concrete Arena implementor. DBFS should accept an `Arena`-implementing value (or a handle) at construction time.

**What needs to change for AC-4:**
1. Add a `RawNvmeArena` struct that implements `Arena` by translating `arena_create/append/readv` → raw `BlockDevice.read_sector/write_sector` calls. This gives DBFS a second backend target alongside NVFS.
2. DbFsDriver constructor: `fn new(backend: Arena, ...)` (or use composition with a concrete type parameter `<B: Arena>`).
3. Existing NvfsDriver/NvfsPosixDriver consumers: zero changes (they continue using the concrete NVFS arena impl directly).

## Key Gap: Disk Persistence of Intent Log and Checkpoint Ring

The intent log (`examples/nvfs/src/core/intent_log.spl`) explicitly says "No real disk I/O." The checkpoint ring is in-memory. For DBFS crash-safety (AC-5), both must be persisted to `META_DURABLE` arenas. This is the highest-risk gap.
