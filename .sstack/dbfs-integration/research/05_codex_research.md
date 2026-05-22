# Stream E — Codex Research (Design Patterns)

**Date:** 2026-04-28
**Note:** Codex CLI binary is present at `/home/ormastes/.npm-global/bin/codex` but requires interactive auth not available in this session. Direct code analysis of `examples/simple_db/` and `examples/nvfs/` yielded concrete primary-source evidence that supersedes external LLM consultation. The design patterns below are derived from actual repo artifacts and are more reliable than Codex output would be for this codebase.

## Top 3 Design Patterns to Copy (from repo evidence)

### Pattern 1: NVFS Arena as BlobBackend (copy from `examples/nvfs/src/core/arena.spl`)

The `Arena` trait (7 verbs: create/append/readv/seal/discard/clone_range/preferred_granule) is already the abstraction DBFS needs for its extent storage. This is the "SQLite VFS pattern" analog: instead of SQLite's file-level VFS, DBFS uses the arena-level abstraction. Recovery invariant: `arena_seal(h, gen)` freezes the arena; appends after seal fail; recovery replays only sealed generations; `arena_discard` is idempotent.

### Pattern 2: Simple DB WAL-then-Publish Protocol (copy from `examples/simple_db/src/engine/wal.spl` + `checkpoint.spl`)

Simple DB implements the WiredTiger-style checkpoint+log pattern: WAL record appended to `DB_WAL` arena → pmap publish via atomic CAS → checkpoint seals WAL + main arenas → new checkpoint ring entry published to `META_DURABLE`. Recovery: find latest clean checkpoint ring entry → replay WAL from `intent_log_head` LSN → discard orphaned uncommitted arenas. DBFS should copy this exact sequence, substituting `Rel/BlkNo` for `Ino/DirEntryKey`.

### Pattern 3: NVFS pmap_btree as Namespace Index (copy from `examples/nvfs/src/core/pmap_btree.spl`)

The `PmapBTree` is a full node-pool B-tree with CLRS top-down proactive fix-up and delete rebalancing. It uses composite i64 keys `(arena_id, offset)`. DBFS needs a namespace B-tree keyed on `(parent_ino: i64, name_hash: i64)` — structurally identical. Copy `pmap_btree.spl`, substitute `PmapKey` → `DentryKey(parent_ino, name_hash)`, `PmapSidecarEntry` → `DentryEntry(ino, name_len, file_type)`. This avoids building a new B-tree from scratch.

## Recovery Invariants Checklist (for Phase 3 design)

- [ ] WAL record must be durable (arena_append with DURABLE_GROUP_COMMIT) before pmap publish
- [ ] Pmap publish is atomic CAS; only succeeds if WAL LSN >= record's wal_lsn
- [ ] Checkpoint begin: seal current WAL arena; seal current main arena
- [ ] Checkpoint commit: write CheckpointEntry to META_DURABLE ring with `clean=1`
- [ ] Mount recovery: scan checkpoint ring for latest `clean=1` entry; get `intent_log_head` LSN
- [ ] Replay WAL records from `intent_log_head` forward; skip records after last committed TXN
- [ ] Orphan detection: any arena created after last clean checkpoint and not referenced by pmap is discarded via `arena_discard`
- [ ] `arena_seal` is idempotent; safe to replay
- [ ] Intent log persistence: must flush to META_DURABLE before returning from `wal_append`
- [ ] Superblock LBA must be published atomically (atomic pointer record via capability-gated CAS)

## Gaps Identified vs. What Repo Has

| Component | Status | Gap |
|---|---|---|
| WAL writer (append/flush/CRC) | EXISTS in Simple DB/engine/wal.spl | Needs DBFS-specific record types (INODE/DENTRY ops) |
| Checkpoint ring | EXISTS in examples/nvfs/src/core/checkpoint.spl | In-memory only; needs META_DURABLE disk persistence |
| Intent log | EXISTS in examples/nvfs/src/core/intent_log.spl | In-memory only; needs disk persistence |
| B-tree | EXISTS in examples/nvfs/src/core/pmap_btree.spl | Key type needs generalization |
| Arena/extent storage | EXISTS (Arena trait + concrete impl) | Need RawNvmeArena implementing Arena over BlockDevice |
| Buffer manager | EXISTS in Simple DB/engine/buffer_mgr.spl | Tied to Rel/BlkNo; needs Ino/BlkNo variant |
| Power-cut harness | NOT EXISTS | Must build for AC-5 |
| DBFS catalog schema | NOT EXISTS | Must design 11 table types |
