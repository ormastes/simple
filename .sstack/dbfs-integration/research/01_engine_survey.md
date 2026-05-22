# Stream A — Engine Survey

**Date:** 2026-04-28

## Finding: No SQLite-class engine exists as a standalone module — but Simple DB + NVFS together constitute a full engine

### Candidate 1: `simple_db_if` + `examples/simple_db/` (RECOMMENDED REUSE TARGET)

**Module path:** `src/lib/nogc_sync_mut/simple_db_if/` (trait contracts) + `examples/simple_db/src/engine/` (concrete impl)

**Status:** PARTIALLY IMPLEMENTED — trait contracts are complete, concrete engine has substantial real code.

**Components present:**
- `simple_db_if/storage_api.spl` — `BufferManager`, `WalWriter`, `PageStore`, `PageMap`, `TempStore`, `Checkpointer`, `BlobStore`, `Vacuumer` traits (8 traits, all signature-complete)
- `simple_db_if/types.spl` — `Rel`, `BlkNo`, `Lsn`, `TxnId`, `PhysPtr` newtype aliases
- `examples/simple_db/src/engine/wal.spl` — WalWriter impl: M1 in-memory + M2 arena-backed; real CRC32C, LE encoding, group-commit, WAL record layout (28-byte header)
- `examples/simple_db/src/engine/buffer_mgr.spl` — BufferManager impl: clock-sweep eviction, dirty tracking, M4 TierCache hook
- `examples/simple_db/src/engine/checkpoint.spl` — Checkpointer impl: `checkpoint_begin`/`checkpoint_commit`
- `examples/simple_db/src/engine/pmap.spl` — PageMap impl: two-level indirection
- `examples/simple_db/src/engine/txn.spl` — MVCC xmin/xmax
- `examples/simple_db/src/engine/brin.spl` — BRIN index
- `examples/simple_db/src/engine/vacuum.spl` — Vacuumer
- `examples/simple_db/src/engine/nvfs_shim.spl` — NVFS adapter
- Tests: `wal_test.spl`, `wal_recovery_test.spl`, `brin_test.spl`, `page_test.spl`, `hot_test.spl`, integration E2E test

**Capabilities present:**
- Pager (8 KiB pages, BufferManager with pinning): YES
- WAL (append, group-commit, flush, CRC32C, LSN): YES (M2 arena-backed)
- Checkpoint (begin/commit/recovery): YES
- MVCC (xmin/xmax per tuple): YES (B-tree-based BRIN, HOT)
- Blob store: YES (trait + impl)
- Vacuum (dead-tuple reclaim): YES

**Capabilities missing for DBFS reuse:**
- B-tree for namespace/dentry (pmap_btree keys on `(arena_id, offset)` — NVFS-specific; needs a general `(name, parent_ino)` B-tree variant)
- No `inode / dentry / file_version / extent_ref` schema tables (Simple DB is row-oriented around `Rel/BlkNo`; DBFS needs filesystem-specific catalog tables)
- No standalone pager (Simple DB's BufferManager is tied to Simple DB's `Rel`/`BlkNo` abstraction — DBFS needs a generic page cache)
- WAL wal_flush is tied to NVFS `arena_append_aligned` — DBFS needs to wire this to its own block device path

### Candidate 2: `examples/nvfs/src/core/pmap_btree.spl`

A full in-memory B-tree implementation (CLRS-style, top-down proactive fix-up, delete rebalancing). Keys: `PmapKey = (arena_id, offset)`. **This IS a reusable B-tree structure** — keyed on composite i64 pair. Could be generalized with a new key type `(parent_ino: i64, name_hash: i64)` for DBFS dentry lookup.

### Candidate 3: `examples/nvfs/src/core/intent_log.spl`

In-memory append-only intent log. op_codes: arena_create (1), arena_seal (2), arena_discard (3). **No real disk I/O yet** — in-memory placeholder. But structure is usable as WAL scaffolding.

### Candidate 4: `examples/nvfs/src/core/checkpoint.spl`

Checkpoint ring (4096 slots, CheckpointEntry with generation/timestamp/superblock_lba/intent_log_head/root_pmap_record_lba). In-memory currently. Structure maps directly to what DBFS needs for durable root publication.

### Recommendation: REUSE Simple DB engine components, do NOT build fresh

**Reuse target:** `examples/simple_db/src/engine/` + `examples/nvfs/src/core/`

**Rationale:** The Simple DB engine has WAL, MVCC, checkpoint, buffer management, and BRIN already implemented. The design doc note about "`from_simple_db` argues against inverting the layering" is confirmed: Simple DB sits ABOVE NVFS (consumes arena_* API), so DBFS should do the same — not try to embed Simple DB. DBFS should reuse the **simple_db storage API pattern** (8 simple_db_if traits) as its own interface pattern, reuse `pmap_btree` for its namespace B-tree, reuse the checkpoint ring for durable root, and wire a new `DbFsWalWriter` onto the existing NVFS `arena_append` path.

**Gap list for Phase 3 arch:**
1. Need DBFS-specific catalog schema as page-structured relations: INODE, DENTRY, FILE_VERSION, EXTENT_REF, EXTENT, BLOCK_BLOB, XATTR, ACL_ENTRY, TXN, WAL_RECORD, STORAGE_CLASS
2. Need a filesystem-key B-tree variant of `pmap_btree` (key: parent_ino + name, not arena_id + offset)
3. Need a `DbFsEngine` struct composing the 8 simple_db_if traits (rather than Rel/BlkNo it uses Ino/DirEntryKey)
4. Intent log needs disk persistence (currently in-memory only in NVFS)
5. Checkpoint ring needs to persist to META_DURABLE arena (currently in-memory)
6. No power-cut simulation harness yet (AC-5 requirement)
