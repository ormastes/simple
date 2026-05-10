# spostgre Engine Design

- **Feature:** `spostgre-nvfs-storage` (SStack `.sstack/spostgre-nvfs-storage/`)
- **Phase:** 3-arch
- **Status:** v0 — Phase 3 design deliverable
- **Last-updated:** 2026-04-18
- **Author:** spostgre track (Claude solo; Codex unavailable per state file)
- **Related:**
  - `../01_research/spostgre_research.md` — Phase 2 research (1358 lines)
  - `./nvfs_design.md` — NVFS filesystem design (companion)
  - `./nvfs/from_spostgre.md` — upfront fs-API contribution from this engine
  - `./nvfs/svllm_requirements.md` — parallel upfront contribution from svllm
  - `../04_architecture/mdsoc_architecture_tobe.md` — MDSOC+ architecture (§MDSOC+ userland for cross-refs)

---

## 1. Scope and non-goals

### 1.1 Scope

**spostgre** is a PostgreSQL-compatible relational engine for Simple that:

- Keeps PostgreSQL's conceptual model: 8 KiB pages, MVCC with xmin/xmax, HOT updates, per-relation forks, BRIN indexing, WAL-first durability, TOAST.
- Replaces PostgreSQL's physicalization layer: pages never update in-place on flash; every update appends a new page to an NVFS arena and bumps a page-indirection map (`rel.pmap`).
- Uses the 7 forks: `main / fsm / vm / pmap / wal / temp / blob` (4 PG-native, 3 spostgre-native).
- Is **MDSOC+**: outer MDSOC capsule (modules, dependencies, side-effects, capabilities, ownership) wraps an inner ECS business layer (components, systems, change-detection).
- Consumes NVFS through the S1–S7 API contract in `./nvfs/from_spostgre.md`.
- Ships in milestones: **M1** = sync engine + WAL + BRIN + pmap; **M2** = out-of-place writes; **M3** = BRIN-HOT-logical; **M4** = tiered cache; **M5** = ZNS / FDP placement.

### 1.2 Non-goals

- **Not PG wire-protocol compatible at M1.** Wire protocol (libpq) lands at M2 or later.
- **Not a distributed engine.** Single-node. Replication is post-M5.
- **Not a general SQL planner rework.** M1 uses PG-style heuristic plans with NVMe-aware cost constants; real cost-model rework is M4+ (research OQ-8).
- **No built-in KMS.** Encryption at-rest is an NVFS concern.
- **No `gc_*` runtime family.** M1–M2 are `nogc_sync_mut`; AIO at M3 moves to `nogc_async_mut`.
- **No user-defined functions / extensions at M1.** Extension API at M5+.
- **No BRIN correctness proofs.** BRIN is best-effort range index; query planner must fall back to sequential scan when BRIN rejects unsafe ranges.

---

## 2. MDSOC outer — five axes

### 2.1 Modules

Per CLAUDE.md "MDSOC+ by default" and the 1-dev state's MDSOC+ placement, spostgre lives in these namespaces:

| Namespace | Path | Role | New/Modified |
|---|---|---|---|
| Trait contracts (shared) | `src/lib/nogc_sync_mut/storage/` | Cross-feature storage types: `Generation`, `SealToken`, `PublishResult`, `Durability`, `StorageClass` re-exports | New |
| spostgre trait contracts | `src/lib/nogc_sync_mut/spostgre_if/` | **(name committed in this design)** — public trait contracts: `PageStore`, `WalWriter`, `BufferManager`, `PageMap`, `Vacuumer`, `Checkpointer`, `RelationOracle` | New |
| Engine implementation | `examples/spostgre/src/engine/*` (submodule) | Concrete impls of spostgre_if traits; buffer pool, WAL writer, MVCC, BRIN, HOT, pmap, recovery | New |
| ECS business layer | `examples/spostgre/src/business/*` (submodule) | Components (Relation / PageDescriptor / Tuple / WalRecord / Txn / Checkpoint / ...) and Systems (sys_commit, sys_wal_flush, ...) over `std.ecs` | New |
| CLI (tool) | `examples/spostgre/src/tool/*` (submodule, symlinked to `src/app/spostgre/`) | `spostgre` CLI: init, wal-replay, vacuum, checkpoint-now, dump-catalog | New |

> **Decision (committed here):** the trait-contract namespace is `spostgre_if` — matches the existing `fs/nvfs/` sibling pattern. Phase 4/5 shall not re-litigate this name.

### 2.2 Dependencies

| spostgre depends on | Why |
|---|---|
| `src/lib/nogc_sync_mut/storage/` | Shared storage types |
| `src/lib/nogc_sync_mut/fs/nvfs/` | NVFS trait contracts (arena_*, atomic_pointer_record_publish, fs_caps) |
| `src/lib/nogc_sync_mut/ecs/` | ECS primitives: `World`, `ComponentStore<T>`, `Query`, `ChangeTracker`, `Entity` |
| `std.common.text` | SQL lexer, identifier handling |
| `std.common.math` | Numeric types, decimal arithmetic |
| `std.common.crypto` | CRC32C for WAL, page checksums |
| `std.common.encoding` | LE u16/u32/u64 codec for on-disk records |
| (not yet) `std.io_runtime` | Only the CLI touches it; engine does not |

| Depends on spostgre | Why |
|---|---|
| `src/app/spostgre` (symlink) | CLI binary |
| `test/` specs | Phase 4 SPipe harness |

**No circular dependencies.** Verified: NVFS has no dependency on spostgre; ECS has no dependency on spostgre; `spostgre_if` has no dependency on the `engine` impl (traits-only).

### 2.3 Side effects

| Effect | Scope | Contained in |
|---|---|---|
| Disk I/O (via NVFS) | Arenas for every fork | `engine/arena_client.spl` |
| Memory allocation | Buffer pool, pmap cache, WAL in-flight ring | `nogc_sync_mut` bounded regions |
| Thread creation | WAL writer (1), checkpointer (1), vacuum (1 or 0), buffer I/O (0 at M1, N at M3) | `engine/threads.spl` |
| Time reads | WAL record timestamps, checkpoint ring, MVCC xmin/xmax | Monotonic clock |
| Randomness | Txn ID salt at boot; BRIN bloom seeds | Bounded |
| NVMe Flush / FUA | Via NVFS durability flags | `engine/wal.spl` |

**Effect discipline:** no side effect occurs in a "pure" layer — the query planner, MVCC predicates, BRIN summary computation, and page-content parsing are all deterministic and effect-free.

### 2.4 Capabilities

| Capability | Holder | Purpose |
|---|---|---|
| `cap_nvfs_client` | engine root | Issue arena_* calls to NVFS |
| `cap_time_mono` | engine root | Monotonic clock reads |
| `cap_thread_spawn` | engine root (M1 bounded) | WAL writer + checkpointer |
| `cap_atomic_publish` | engine root | pmap-root CAS |
| `cap_spostgre_admin` | CLI only | admin operations (vacuum, checkpoint-now) |

The spostgre capsule never forwards `cap_nvme_ns_open` or any raw NVFS driver capability — all I/O is mediated by the NVFS capsule.

### 2.5 Ownership

| Subsystem | Owns |
|---|---|
| BufferManager | `BufferFrame` components; page-in / page-out |
| WalWriter | `WalRecord` components in-flight; group-commit queue |
| Checkpointer | `Checkpoint` components; pmap-root CAS; sealed arena set |
| Vacuumer | `SegmentSummary` components; dead-tuple reclaim |
| PageMap | `PageMapEntry` components; two-level root |
| RelationOracle | `Relation` components; catalog |
| TempManager | `TempSpill` components; DB_TEMP arena |
| BlobStore | `BlobRef` components; rel.blob arena |

Each subsystem owns its component store exclusively. Systems read other stores via Query<A, B>; they do not mutate other subsystems' stores.

---

## 3. ECS business layer (inner)

Per MDSOC+ for userland, spostgre uses the ECS primitives in `src/lib/nogc_sync_mut/ecs/`.

### 3.1 Components (POD structs)

| Component | Field | Type | Purpose |
|---|---|---|---|
| **`Relation`** | `oid` | `u64` | Relation OID |
|  | `namespace_oid` | `u64` | Schema / namespace |
|  | `relkind` | `u8` | 'r'=heap, 'i'=index, 't'=toast |
|  | `main_arena_id` | `ArenaId` | rel.main fork |
|  | `pmap_root_slot` | `StaticStr` | Slot name for atomic publish |
|  | `live_version` | `Generation` | Current pmap generation |
|  | `col_count` | `u16` | Number of columns |
| **`PageDescriptor`** | `rel_oid` | `u64` | Owning relation |
|  | `logical_page_no` | `u64` | Logical page number |
|  | `physical_arena_id` | `ArenaId` | Current holder |
|  | `physical_offset` | `u64` | Offset within arena |
|  | `page_generation` | `Generation` | For HOT-logical chain |
|  | `checksum` | `u32` | CRC32C |
|  | `flags` | `u32` | bit0=has_hot, bit1=pinned, bit2=blob_overflow |
| **`Tuple`** | `rel_oid` | `u64` | Owning relation |
|  | `tid_page` | `u64` | Logical page |
|  | `tid_slot` | `u16` | Line-pointer slot |
|  | `xmin` | `u64` | Inserting txn |
|  | `xmax` | `u64` | Deleting txn (0 = live) |
|  | `cmin_cmax` | `u32` | Command IDs packed |
|  | `flags` | `u32` | bit0=hot_updated, bit1=heap_only |
|  | `t_ctid_page` | `u64` | HOT chain successor (logical) |
|  | `t_ctid_slot` | `u16` | |
| **`WalRecord`** | `lsn` | `u64` | Log sequence number (monotonic) |
|  | `prev_lsn` | `u64` | Per-txn backref |
|  | `xid` | `u64` | Transaction |
|  | `rmgr` | `u8` | Resource manager (heap/btree/...) |
|  | `info` | `u8` | Record sub-type |
|  | `body_len` | `u32` | Payload bytes |
|  | `body_offset` | `u64` | Offset into WAL arena |
|  | `crc32c` | `u32` | Record CRC |
| **`Txn`** | `xid` | `u64` | Transaction ID |
|  | `snapshot_xmin` | `u64` | Snapshot lower bound |
|  | `snapshot_xmax` | `u64` | Snapshot upper bound |
|  | `pinned_pmap_gen` | `Generation` | Pinned pmap generation |
|  | `status` | `u8` | 0=running, 1=committed, 2=aborted |
|  | `commit_lsn` | `u64` | LSN at commit (0 if running) |
| **`Checkpoint`** | `gen` | `Generation` | Checkpoint generation |
|  | `redo_lsn` | `u64` | Redo point |
|  | `sealed_arena_set` | `[ArenaId]` | Arenas sealed at this checkpoint |
|  | `pmap_root_record_gen` | `Generation` | Publish generation |
|  | `timestamp_ns` | `u64` | Monotonic |
| **`BufferFrame`** | `frame_id` | `u32` | Pool slot |
|  | `rel_oid` | `u64` | Owner |
|  | `logical_page_no` | `u64` | Page identity |
|  | `page_generation` | `Generation` | Version tag |
|  | `dirty` | `bool` | Needs writeback? |
|  | `pin_count` | `u16` | Pins |
|  | `last_use_tick` | `i64` | For eviction |
|  | `content_offset` | `u64` | Offset in buffer-pool memory |
| **`PageMapEntry`** | `rel_oid` | `u64` | Relation |
|  | `logical_page_no` | `u64` | Key |
|  | `physical_arena_id` | `ArenaId` | Target arena |
|  | `physical_offset` | `u64` | Offset |
|  | `page_generation` | `Generation` | Version |
|  | `flags` | `u32` | bit0=blob_pointer, bit1=evicted |
| **`SegmentSummary`** | `arena_id` | `ArenaId` | Arena |
|  | `live_bytes` | `u64` | Live payload |
|  | `total_bytes` | `u64` | Arena size |
|  | `dead_tuple_count` | `u32` | Reclaimable |
|  | `min_xid` | `u64` | Oldest visible xid |
|  | `max_xid` | `u64` | Newest xid seen |
| **`TempSpill`** | `spill_id` | `u64` | Session-local ID |
|  | `arena_id` | `ArenaId` | DB_TEMP arena |
|  | `bytes_written` | `u64` | Progress |
|  | `op_kind` | `u8` | 0=sort, 1=hash_build, 2=materialize |
|  | `owner_txn` | `u64` | Parent transaction |
| **`BlobRef`** | `blob_oid` | `u64` | Blob object ID |
|  | `rel_oid` | `u64` | Referring relation |
|  | `arena_id` | `ArenaId` | rel.blob arena |
|  | `offset` | `u64` | Location |
|  | `length` | `u64` | Bytes |
|  | `checksum` | `u32` | CRC |
|  | `refcount` | `u32` | Live references |

All components are POD (no pointers, no GC references). Field-of-component layout is preserved by `std.ecs.ComponentStore<T>`.

### 3.2 Systems (free functions over World)

| System | Input queries | Output effect |
|---|---|---|
| `sys_commit` | `Query<Txn, WalRecord> where Added<WalRecord>`, `Query<Txn> where Changed<Txn>` | Assigns commit_lsn; flushes group-commit queue; bumps Txn.status |
| `sys_wal_flush` | `Query<WalRecord> where Added<WalRecord>` | Coalesces WAL records into aligned-append to DB_WAL arena; invokes NVFS `arena_append_aligned(DURABLE_GROUP_COMMIT)` |
| `sys_buffer_manager` | `Query<BufferFrame>`, `Query<PageDescriptor>` | Pages in on miss; evicts LRU; writes dirty frames via `sys_page_rewrite` hand-off |
| `sys_checkpoint` | `Query<Txn> where Changed<Txn>`, `Query<BufferFrame> where dirty`, `Query<Checkpoint>` | Seals active WAL arena; seals active main arena; issues `atomic_pointer_record_publish` for pmap-root; spawns new Checkpoint entity |
| `sys_vacuum` | `Query<SegmentSummary> where Changed<SegmentSummary>`, `Query<Tuple> where xmax>0 && Removed<Txn>` | Marks dead tuples; compacts logical pages; schedules `arena_discard` when all snapshots drain |
| `sys_page_compact` | `Query<PageDescriptor> where fragmentation>threshold` | Emits a new logical-page-group; invokes `arena_clone_range` for live tuples |
| `sys_temp_sweep` | `Query<TempSpill> where Removed<Txn>` | Drops DB_TEMP arenas when owning Txn completes |
| `sys_stats_collector` | `Query<Relation>`, `Query<SegmentSummary>` | Updates catalog stats for planner; refreshes `FsCaps` from NVFS |

All systems are pure functions `fn sys_x(world: &mut World, ctx: SysCtx)`. Ordering: `sys_wal_flush` before `sys_commit`; `sys_buffer_manager` before `sys_page_compact`; `sys_checkpoint` is serialized against all others via a single "checkpoint tick" in `World`.

### 3.3 Change-detection usage

| System | Uses |
|---|---|
| `sys_commit` | `Added<WalRecord>`, `Changed<Txn>` |
| `sys_wal_flush` | `Added<WalRecord>` |
| `sys_buffer_manager` | (none — per-tick drain) |
| `sys_checkpoint` | `Changed<Txn>`, `dirty` flag on BufferFrame |
| `sys_vacuum` | `Changed<SegmentSummary>`, `Removed<Txn>` |
| `sys_page_compact` | (threshold query, no change detection) |
| `sys_temp_sweep` | `Removed<Txn>` |

Change detection is tick-based per `std.ecs.change_detection` (see `src/lib/nogc_sync_mut/ecs/change_detection.spl`).

---

## 4. On-disk layout — 7 forks

All multi-byte integers little-endian unless noted. Page size 8 KiB.

### 4.1 Fork list

| Fork | NVFS StorageClass | Purpose |
|---|---|---|
| `rel.main` | `GENERAL_MUTABLE` → (after seal) `CHECKPOINT_SNAPSHOT` | Heap pages |
| `rel.fsm` | `GENERAL_MUTABLE` | Free Space Map |
| `rel.vm` | `GENERAL_MUTABLE` | Visibility Map |
| `rel.pmap` | `META_DURABLE` (root), `GENERAL_MUTABLE` (delta) | Page-indirection map |
| `rel.wal` | `DB_WAL` | Write-ahead log |
| `rel.temp` | `DB_TEMP` | Scratch for sort / hash / materialize |
| `rel.blob` | `MODEL_IMMUTABLE` | TOAST / WiscKey-style large values |

### 4.2 Page header (8 KiB page)

```
offset size field
0x0000 4    pd_lsn_lo (u32)         ; LSN low word
0x0004 4    pd_lsn_hi (u32)         ; LSN high word
0x0008 2    pd_checksum (u16)       ; page CRC32C truncated
0x000a 2    pd_flags (u16)          ; bit0=has_hot, bit1=all_visible
0x000c 2    pd_lower (u16)          ; end of line-pointer array
0x000e 2    pd_upper (u16)          ; start of tuple heap
0x0010 2    pd_special (u16)        ; offset to special region
0x0012 2    pd_pagesize_version (u16); 0x8004 = 8 KiB v4
0x0014 4    pd_prune_xid (u32)      ; oldest HOT-pruneable xid
0x0018 8    pd_generation (u64)     ; logical-page generation tag
0x0020 ...  line_pointers[N]        ; 4 bytes each, grow ↓
...
... free space ...
0x1fe0 32   pd_tail_guard (zeros + CRC tail)
```

### 4.3 Tuple header (within a page)

```
offset size field
0x00   4    t_xmin (u32)           ; inserting xid low
0x04   4    t_xmax (u32)           ; deleting xid low
0x08   4    t_cid (u32)            ; cmin/cmax packed
0x0c   6    t_ctid (u48)           ; HOT chain successor (page u32 + slot u16)
0x12   2    t_infomask (u16)       ; bit0=has_null, bit1=heap_only, bit4=hot_updated
0x14   2    t_infomask2 (u16)      ; natts + flags
0x16   1    t_hoff (u8)            ; byte offset to user data
0x17   1    reserved
0x18   ...  user data (aligned)
```

### 4.4 WAL record layout

```
offset size field
0x00   4    xl_tot_len (u32)       ; total bytes incl header
0x04   4    xl_xid (u32) low       ; extend to 64 via prev_lsn chain
0x08   8    xl_prev (u64)          ; previous LSN
0x10   1    xl_rmgr (u8)           ; resource manager
0x11   1    xl_info (u8)           ; sub-type
0x12   2    xl_flags (u16)         ; bit0=has_fpi, bit1=has_blob_ref
0x14   4    xl_crc32c (u32)        ; over bytes 0..xl_tot_len
0x18   ...  body
xl_tot_len - 8  : padding (to group-commit granule)
```

### 4.5 Page-map entry (pmap leaf record)

```
offset size field
0x00   8    logical_page_no (u64)
0x08   8    physical_arena_id (u64)
0x10   8    physical_offset (u64)
0x18   8    page_generation (u64)
0x20   4    flags (u32)            ; bit0=blob_pointer, bit1=evicted
0x24   4    reserved
```

Root of pmap: a 96-byte record published via NVFS `atomic_pointer_record_publish(META_DURABLE, "pmap:<rel_oid>", ...)`. Root carries: level-0 delta offset, level-1 B-tree root offset, live generation, build timestamp.

### 4.6 Free-space summary (rel.fsm page layout)

```
offset size field (repeated per summarized page)
0x00   8    logical_page_no (u64)
0x08   2    free_bytes (u16)       ; 0..8192
0x0a   1    avail_class (u8)       ; 8-bucket free-space class
0x0b   5    reserved
```

### 4.7 Visibility summary (rel.vm page layout)

```
offset size field
0x00   8    logical_page_no (u64)
0x08   1    flags (u8)             ; bit0=all_visible, bit1=all_frozen
0x09   7    reserved
```

### 4.8 Checkpoint ring entry (in META_DURABLE area)

```
offset size field
0x00   8    checkpoint_gen (u64)
0x08   8    redo_lsn (u64)
0x10   8    timestamp_ns (u64)
0x18   8    pmap_root_record_gen (u64)
0x20   8    sealed_wal_arena_id (u64)
0x28   8    sealed_main_arena_id (u64)
0x30   8    oldest_live_xid (u64)
0x38   8    crc32c (u64, high 32 zero)
```

### 4.9 Alignment constraints

- WAL records: padded to `fs_caps().preferred_write_granule` at group-commit boundary.
- Heap pages: 8 KiB aligned on NVFS arena. NVFS ensures this via `arena_append_aligned(granule=8192)`.
- pmap root: single atomic-publish record ≤ 4 KiB.
- rel.blob: aligned to 64 KiB internal chunks for WiscKey-style streaming reads.

---

## 5. Storage API

| Call | Boundary | Purpose |
|---|---|---|
| `buf_get(rel, page) -> PagePtr` | Outer (BufferManager) | Resolve a logical page; may trigger NVFS read |
| `buf_prefetch(rel, pages)` | Outer | Hint prefetch |
| `wal_append(record) -> Lsn` | Outer | Add a WAL record (returns pending LSN) |
| `wal_group_commit(upto_lsn) -> Lsn` | Outer | Wait for durability up to LSN |
| `page_rewrite(rel, page, new_bytes) -> PageGeneration` | Outer | Out-of-place rewrite via arena_append + pmap delta |
| `pmap_publish(rel, root_bytes, expected_gen) -> Generation` | Outer | CAS the pmap root |
| `temp_alloc(txn, op_kind) -> SpillId` | Outer | Allocate a DB_TEMP arena |
| `temp_release(spill)` | Outer | Drop a DB_TEMP arena |
| `checkpoint_begin() -> CheckpointGen` | Outer | Start a checkpoint |
| `checkpoint_commit(gen) -> Result` | Outer | Seal arenas + publish pmap root |
| `blob_put(bytes) -> BlobRef` | Outer | Append to rel.blob |
| `blob_get(blob_ref, buf)` | Outer | Stream-read from rel.blob |
| `vacuum_range(rel, lo..hi)` | Outer | Reclaim dead tuples in a logical range |
| _(inner)_ `compute_page_crc(page) -> u32` | Inner | Pure; no I/O |
| _(inner)_ `mvcc_visible(tuple, snapshot) -> bool` | Inner | Pure; no I/O |
| _(inner)_ `brin_range_covers(summary, pred) -> bool` | Inner | Pure; no I/O |
| _(inner)_ `line_pointer_parse(page, slot) -> TuplePtr` | Inner | Pure; no I/O |

Outer calls are the MDSOC module boundary — any caller crossing the spostgre capsule uses these. Inner helpers are private to the ECS business layer and never escape.

---

## 6. WAL protocol

### 6.1 Record types

| Type | Sub-types | Notes |
|---|---|---|
| `HEAP_INSERT` | `HI_STANDARD`, `HI_HOT`, `HI_BLOB_REF` | New tuple |
| `HEAP_UPDATE` | `HU_STANDARD`, `HU_HOT`, `HU_MOVE_TO_NEW_PAGE` | Update; HOT preserves page |
| `HEAP_DELETE` | `HD_STANDARD` | Dead-tuple marker |
| `COMMIT` | — | Transaction commit |
| `ABORT` | — | Transaction abort |
| `CHECKPOINT` | `CKPT_BEGIN`, `CKPT_COMMIT` | Epoch boundaries |
| `PMAP_DELTA` | — | Page-map change (arena_id + offset + generation) |
| `ARENA_SEAL` | — | Arena sealed at this LSN |
| `ARENA_DISCARD` | — | Arena dropped at this LSN |
| `BRIN_UPDATE` | — | BRIN summary refresh |
| `FULL_PAGE_IMAGE` | `FPI_HEAP`, `FPI_BRIN` | Post-checkpoint first-write full image |

### 6.2 LSN structure

```
63                              32 31                0
+-------------------------------+------------------+
| segment_id (u32)              | byte_offset (u32)|
+-------------------------------+------------------+
```

Segment size = 1 GiB (fits in the u32 offset). LSN monotonic across the system; WAL arena holds ≥ 1 segment.

### 6.3 Group-commit formation

Concurrent `wal_append` calls enqueue to a ring buffer. The WAL-writer thread coalesces when ANY of:

- Buffer reaches `fs_caps().preferred_write_granule` (typically 16 KiB).
- Buffer age exceeds 200 µs (tunable).
- Explicit `wal_group_commit(lsn)` blocks for `lsn ≥ buffer.high_lsn`.

On flush: single `arena_append_aligned(DB_WAL, bytes, granule, DURABLE_GROUP_COMMIT)` — NVFS coalesces further if possible.

### 6.4 Durable-commit handshake

1. `sys_commit` moves Txn to COMMIT-PENDING; enqueues `COMMIT` WAL record.
2. WAL writer adds to group buffer; returns pending LSN.
3. When group flushed, `arena_group_commit` returns the highest durable LSN.
4. `sys_commit` awakens waiters; their Txn becomes COMMITTED.

Commit is **not** visible to other transactions until the durable-LSN cursor crosses the Txn's commit LSN. This preserves PG's read-committed semantics while keeping group-commit throughput high.

### 6.5 NVMe Flush / FUA usage

- `Durability::DURABLE_ON_RETURN` → NVFS uses FUA bit if supported, else Write + Flush.
- `Durability::DURABLE_GROUP_COMMIT` → NVFS coalesces writes, issues one Flush per group.
- `Durability::BUFFERED` → NVFS returns on CQ; no Flush. Used only for BRIN summaries and catalog hints.

### 6.6 Atomicity-limits awareness (research §6)

If device AWUPF ≥ 8 KiB, heap page writes are atomic. Otherwise:
- spostgre writes a FULL_PAGE_IMAGE to WAL on first modification after checkpoint.
- On recovery, if heap page CRC fails, replay the FPI.
- This matches PG 18 `full_page_writes=on` semantics.

### 6.7 Recovery algorithm

```
1. Mount NVFS; get fs_caps() and the set of META_DURABLE records.
2. Read checkpoint ring; pick highest valid checkpoint_gen.
3. Epoch selection: the Checkpoint.redo_lsn is the replay start.
4. Scan WAL arena forward from redo_lsn:
   a. For each record: verify xl_crc32c.
   b. Apply according to rmgr: heap insert/update/delete, pmap delta, etc.
   c. Mark arena_seal / arena_discard records as observed.
5. Reconcile pmap-root record: if checkpoint says gen=G, but NVFS current
   pmap record gen=G' > G, trust NVFS (a later checkpoint made durable
   metadata without WAL-record-of-checkpoint persisting — partial crash).
6. Drop all DB_TEMP arenas (NVFS already does this; spostgre confirms).
7. Rebuild buffer pool from main arenas (lazy — on demand).
8. Declare engine ready; accept queries.
```

Recovery is **redo-only**. No undo log: uncommitted transactions are invisible via MVCC `xmin > snapshot.xmax`; dead tuples are reaped by vacuum.

---

## 7. MVCC with HOT-at-logical-page-scope

### 7.1 Visibility rules (unchanged from PG)

A tuple is visible to snapshot S iff:
- `t_xmin < S.xmax`
- `t_xmin` committed before S was taken (or is the observer's own Txn)
- `t_xmax == 0` OR `t_xmax ≥ S.xmax` OR `t_xmax` uncommitted

### 7.2 xmin/xmax handling

- Txn IDs are 64-bit; no wrap-around handling needed at PG scale.
- `t_xmin` / `t_xmax` on disk are 32-bit low words; high word is carried via the `Txn` component in memory and the catalog's `oldest_live_xid`.
- On recovery, Txn high-word is reconstructed from the checkpoint's `oldest_live_xid`.

### 7.3 HOT chain in logical-page-group

Traditional PG HOT: all tuples in a HOT chain live on the same physical page.

**spostgre HOT-logical:** all tuples in a HOT chain live on the same **logical** page group (same `logical_page_no`, possibly different `page_generation`).

- Update creates a new page-version: append new page to arena, update pmap, bump page_generation.
- HOT chain head tuple's `t_ctid` points at the next slot within the (logical_page_no, page_generation+1) pair.
- Readers following a HOT chain resolve `(logical_page_no, t_ctid.slot)` through pmap to the physical arena offset.
- Prune: when all HOT versions are dead, pmap is updated to point at the latest live page-version; older generations become eligible for vacuum.

Gain: HOT updates still avoid index bloat (same `tid_page`), but we don't need in-place updates for HOT correctness. Loss: pmap traversal adds ~100 ns per HOT resolve vs PG's direct page access.

### 7.4 Prune semantics

`sys_vacuum` identifies prunable HOT chains by scanning `Tuple` components where all `xmax != 0 && xmax committed before oldest_live_snapshot`. Prune rewrites the chain-head slot to point at the final live descendant, then clears intermediate slots.

---

## 8. BRIN-first indexing policy

### 8.1 When BRIN is chosen

BRIN summaries fit naturally with arenas (no rebalancing). spostgre auto-creates BRIN when:

- Relation size > 128 MiB (heuristic).
- Column is indexed with `btree` AND stats show sequential correlation > 0.9 (range-scannable).
- User explicitly `CREATE INDEX USING brin(...)`.

### 8.2 Fallback to B-tree

- Low-correlation columns → B-tree at M4. Until M4, spostgre uses sequential scan for equality lookups on non-BRIN-qualifying columns.
- UNIQUE and PRIMARY KEY constraints require B-tree; M1 accepts them but warns that uniqueness is enforced via full-relation scan until M4.

### 8.3 BRIN summary format

Per range (default range = 128 pages = 1 MiB logical):

```
offset size field
0x00   8    logical_page_start (u64)
0x08   4    page_count (u32)
0x0c   4    null_count (u32)
0x10   8    min_value (u64)          ; type-specific encoding
0x18   8    max_value (u64)
0x20   8    bloom_bits (u64)         ; 64-bit bloom, ~4 hash fns
0x28   8    generation (u64)         ; BRIN refresh tag
```

---

## 9. Out-of-place write pipeline

```mermaid
sequenceDiagram
    participant T as Txn (client)
    participant BM as BufferManager
    participant WW as WalWriter
    participant NVFS_WAL as NVFS DB_WAL
    participant NVFS_MAIN as NVFS GENERAL_MUTABLE
    participant PM as PageMap
    participant CP as Checkpointer

    T->>BM: UPDATE ...
    BM->>BM: copy-on-write page in pool; mark dirty
    BM->>WW: wal_append(HEAP_UPDATE)
    WW->>NVFS_WAL: arena_append_aligned(DURABLE_GROUP_COMMIT)
    NVFS_WAL-->>WW: offset + durable-LSN
    WW-->>T: commit_lsn visible
    BM->>NVFS_MAIN: arena_append(new_page_bytes) [async at M3; sync at M1]
    NVFS_MAIN-->>BM: (arena_id, offset, gen)
    BM->>PM: publish pmap delta entry (logical_page_no -> (arena, offset, gen))
    note over PM: pmap delta kept in memory + in-place update to delta record until compact
    CP->>CP: on checkpoint tick
    CP->>NVFS_MAIN: arena_seal(active_main_arena)
    CP->>PM: compact delta into B-tree; serialize pmap root record
    CP->>NVFS_WAL: atomic_pointer_record_publish("pmap:<rel>", bytes, expected_gen)
    NVFS_WAL-->>CP: new generation
    CP->>CP: async schedule arena_clone_range for live pages; arena_discard old
```

Step-by-step:

1. **WAL append first.** Record is durable before page is written.
2. **Durable commit LSN visible.** Client sees commit.
3. **Append update segment.** New page-version goes to active main arena.
4. **Publish pmap delta.** In-memory pmap delta updated; durable delta entry in rel.pmap delta arena.
5. **Async compact.** Checkpointer folds delta into B-tree at next epoch.
6. **Discard old.** Once all snapshots pinning the old generation age out, NVFS `arena_discard` reclaims the old main arena.

---

## 10. Recovery

### 10.1 Startup

**Preconditions:** NVFS mounted; META_DURABLE records readable; checkpoint ring valid; DB_WAL arena readable.

**Postconditions:** engine fully consistent; all committed transactions durable and visible; no uncommitted tuples visible; temp arenas dropped; pmap root published.

### 10.2 Algorithm (summary — full details in §6.7)

1. Read `FsCaps`; cache capabilities.
2. Read checkpoint ring; pick highest valid.
3. Redo-only WAL replay from `redo_lsn`.
4. Reconcile pmap-root with NVFS current record.
5. Drop DB_TEMP (NVFS does this; spostgre confirms).
6. Open for queries.

### 10.3 Crash-point matrix

| Crash point | Visible state | Recovery action |
|---|---|---|
| Before WAL record durable | No COMMIT visible; txn invisible to others | Nothing to redo; txn is as-if-never |
| After WAL durable, before arena_append | WAL has HEAP_UPDATE; no physical page yet | Redo replays: re-append page to fresh arena; update pmap delta |
| After arena_append, before pmap delta publish | Physical page exists; pmap still points at old | Redo detects orphan page via WAL PMAP_DELTA record; re-publishes delta |
| After pmap delta, before checkpoint | delta-record has entry; pmap-root still old | Next checkpoint absorbs delta; no redo needed |
| After checkpoint arena_seal, before pmap-root CAS | Sealed arena written; pmap-root still old | Redo sees CHECKPOINT_BEGIN but not CHECKPOINT_COMMIT; replays pmap delta compaction |
| After pmap-root CAS, before WAL CHECKPOINT_COMMIT | NVFS holds new generation; WAL missing commit record | Reconcile step trusts NVFS; writes synthetic CHECKPOINT_COMMIT during redo |
| After CHECKPOINT_COMMIT, before arena_discard | Stale arenas exist but unreferenced | Vacuum will reap later; no correctness issue |
| Mid-arena_discard | NVFS state atomic; either discarded or not | NVFS handles; spostgre sees consistent state |

---

## 11. NVFS interface assumptions

This design depends on the upfront fs-contribution in `./nvfs/from_spostgre.md`. The following table maps each engine storage-API call to its NVFS S-entry:

| Storage API call (§5) | NVFS S-entry |
|---|---|
| `buf_get` → underlying `arena_read` / `arena_readv` | baseline NVFS (N2) |
| `buf_prefetch` | `arena_set_hint(SEQUENTIAL)` (S-stretch implicit via hints) |
| `wal_append` + `wal_group_commit` | **S2** (`arena_append_aligned`) + **S7** (`arena_flush`) |
| `page_rewrite` | **S1** (`arena_create` for new epoch) + `arena_append` + pmap delta |
| `pmap_publish` | **S6** (`atomic_pointer_record_publish`) |
| `temp_alloc` / `temp_release` | **S1** + **S3** (`arena_discard`) with `DB_TEMP` class |
| `checkpoint_begin` | `arena_seal` + **S6** |
| `checkpoint_commit` | **S3** (`arena_seal`) + **S6** + **S3** (`arena_discard` with gen pin) |
| `blob_put` / `blob_get` | **S1** (MODEL_IMMUTABLE) + `arena_append` + `arena_read` |
| `vacuum_range` | **S3** (`arena_discard` with gen pin) + **S4** (`arena_clone_range`) |

Six primary FR candidates from research (§11.7) map thus:
- `arena_create` / per-fork class → **S1**
- aligned-append WAL → **S2**
- `arena_seal` + generation-pinned discard → **S3**
- `arena_clone_range` → **S4**
- capability-probed CAS → **S6**
- preferred I/O granule → **S5**

---

## 12. Phased milestones

### M1 — WAL + heap skeleton (10 weeks, 1 eng)

**Dependencies:** NVFS N2 (arena baseline on conventional NVMe).

**Deliverables:**
- BufferManager with fixed-size pool.
- WalWriter with synchronous group-commit (single thread).
- Heap page format + line-pointers + tuple headers.
- MVCC (no HOT yet — updates are delete+insert).
- Redo-only recovery.
- CLI: `spostgre init`, `spostgre wal-replay`, `spostgre catalog-dump`.
- SPipe: crash-injection tests at each crash-point matrix row.

**Acceptance:**
- Insert 1 M rows, crash, replay: zero row loss, zero phantom rows.
- Sustained commit rate ≥ 10 K ops/s on baseline NVMe (after SSD-iq preconditioning).
- Every Phase-4 AC passes against M1 binary.

### M2 — pmap + out-of-place writes (8 weeks, 1 eng)

**Dependencies:** NVFS N2 complete; begin NVFS N3 dependency.

**Deliverables:**
- Page-indirection map (delta + B-tree).
- pmap-root atomic publish via NVFS S6.
- Checkpoint sealing arenas; generation-pinned discard.
- `arena_clone_range` integration (fallback path OK).
- Recovery step 5 (NVFS-reconcile).

**Acceptance:**
- Update-heavy workload shows zero in-place page writes (confirmed via NVFS counter).
- Checkpoint cycle p99 ≤ 2 s on a 1 GiB database.
- 1 TiB-pmap test (synthetic; page-count only) — two-level root fits in ≤ 64 MiB RAM.

### M3 — BRIN + HOT-logical (8 weeks, 1 eng)

**Dependencies:** NVFS N3 complete (real capabilities); async runtime family transition.

**Deliverables:**
- BRIN index as M1-default range index.
- HOT-at-logical-page-scope.
- `sys_page_compact` emits compacted page-versions.
- AIO read path (buf_get becomes async).
- Pinned-buffer registration (NVFS fs_register_buffer).

**Acceptance:**
- BRIN range-scan at 500 MB/s sustained on NVMe.
- HOT-heavy workload shows ≥ 30 % reduction in physical-page churn vs M2.
- AIO pipeline keeps ≥ 90 % queue depth at target throughput.

### M4 — Tiered local-NVMe cache below DRAM (6 weeks, 1 eng)

**Dependencies:** NVFS N3.

**Deliverables:**
- Secondary cache on a separate NVFS arena (GENERAL_MUTABLE, `class_hint=cache`).
- Evicted pages moved to cache, not discarded.
- Planner cost constants for `cache_hit_cost` (OQ-8 addressed partially).

**Acceptance:**
- Cache-hit ratio ≥ 80 % on TPC-C warm run after eviction pass.
- Tail-latency improvement ≥ 25 % on skewed workload.

### M5 — ZNS / FDP placement hints (6 weeks, 1 eng)

**Dependencies:** NVFS N4 (ZNS) + N5 (FDP) complete.

**Deliverables:**
- `StorageClass` → FDP PID mapping validated end-to-end.
- WAL on ZNS Zone Append when available.
- CHECKPOINT_SNAPSHOT arenas on ZNS sealed zones.
- Benchmark discipline: published sustained-WAF numbers per class.

**Acceptance:**
- On FDP-capable drive, device WAF ≤ 1.3 on mixed OLTP workload.
- On ZNS-capable drive, spostgre + svllm coexist without zone-budget starvation.

---

## 13. Open questions

Carried from Phase 2 research (§12: OQ-1..OQ-15) plus new OQs raised here:

- **OQ-1.** Polymorphic Page representation: tagged union vs trait object. M1 uses tagged union. Revisit at M4 for index-AM polymorphism.
- **OQ-2.** Global WAL vs per-relation WAL. M1 = global. Per-relation at M5 if needed.
- **OQ-3.** WAL record framing: PG-compat vs spostgre-native CRC32C. **Design decision: spostgre-native.** PG-compat framing sacrifices alignment flexibility; we prefer aligned-append discipline.
- **OQ-4.** pmap data structure: two-level (delta + B-tree) chosen for M2. Alternatives (AMT, radix) are M4+ concerns.
- **OQ-5.** Blob pointer indirection depth: 1 level at M1 (rel.blob offset); 2 levels (blob group → blob offset) at M5 for 10 B+ blob counts.
- **OQ-6.** HOT chain arena placement: same arena as base tuple (M1); dedicated hot-spill arena at M3 (researchable).
- **OQ-7.** Checkpoint frequency policy. M1 = every 30 s or 512 MiB of WAL, whichever first. Tunable.
- **OQ-8.** Planner cost model on NVMe. Hardcoded constants at M1-M3. Real rework at M4 concurrent with tiered cache.
- **OQ-9.** Recovery strategy. Redo-only confirmed.
- **OQ-10.** Benchmark preconditioning encoding: SSD-iq full-device-write cycle before every measurement; scripted in Phase 5 test harness.
- **OQ-11.** PG wire protocol timing. M2 or M3.
- **OQ-12.** Catalog bootstrap sequence. Bootstrap relations (pg_class, pg_attribute) live in a dedicated META_DURABLE arena created at `spostgre init`.
- **OQ-13.** Extension API. M5+.
- **OQ-14.** MVCC × pmap-generation concurrency. Design: each Txn pins its `pinned_pmap_gen`; `arena_discard` respects this; snapshots drain over time.
- **OQ-15.** Vacuum granularity: per-relation (M1) → per-arena (M3).
- **OQ-16 (new).** What is the cost model for `arena_clone_range` in a no-copy-offload world? Quantify per-page CPU cost at M2 so M4 planner knows.
- **OQ-17 (new).** Interaction between spostgre checkpointer and svllm tensor_pack seals on a shared NVFS mount — do they interfere on open-zone budget in ZNS mode? Coordinate with svllm in Phase 5.
- **OQ-18 (new).** Should `sys_vacuum` be a system at all, or a separate mini-capsule? Keeping it inline simplifies change-detection; isolating it improves fault containment. Tentatively inline.

---

## 14. Design tensions carried to Phase 4

From research §3 tensions and this design's own reconciliation:

1. **pmap size vs RAM** — two-level design solves M2; real-world 1 TiB datasets deferred to M4 validation.
2. **CAS capability-probe path** — two commit paths live in code forever; the API contract (S6) hides this from callers, but tests must cover both.
3. **MVCC correctness under arena seal + discard** — generation pinning is the correctness invariant. Spec at Phase 4 must test it under adversarial snapshot-hold durations.
4. **Query planner on NVMe** — hardcoded constants at M1-M3 will give wrong plans for some workloads. Mitigated by encouraging BRIN use (M1) and deferring hard cases to M4 cost-model rework.
5. **Benchmark honesty** — SSD-iq preconditioning is mandatory in Phase 5 harness. Design decision recorded here; Phase 4 spec must reference it.
