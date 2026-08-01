# Simple DB Full Engine & DBFS Hardening Audit

**Date:** 2026-05-23
**Analyst:** Research agent (Sonnet 4.6)
**Scope:** Full engine tier (`examples/simple_db/`), DBFS layer (`test/dbfs/`, `src/lib/*/db/`), shared interface (`simple_db_if/`), storage lib (`storage/`), NVFS requirements, SIMD acceleration

---

## 1. Current Capabilities (What Exists and Works)

### Architecture Reality

The design doc names `examples/simple_db/src/engine/*` as the "concrete impl" (submodule). In practice, **that submodule is empty**: `examples/simple_db/` contains only `.git` (a gitlink file), `.simple/` (test cache artifact), and `target/`. No `src/` directory exists there. The engine implementation that _does_ exist lives entirely in the stdlib:

- `src/lib/nogc_sync_mut/db/dbfs_engine/` — 18 files, ~3,986 lines (sync variant)
- `src/lib/nogc_async_mut/db/dbfs_engine/` — 18 matching files (async variant)
- `src/lib/nogc_sync_mut/storage/shared/` — btree, WAL, checkpoint_ring, intent_log (~1,198 lines)
- `src/lib/nogc_sync_mut/db/` — accel.spl (664L), query_planner.spl (288L), ml_cost_model.spl (151L), dbfs_driver/ (~684L)

### What Is Functionally Implemented

| Component | Status | Notes |
|-----------|--------|-------|
| BTree (storage/shared/btree.spl) | Implemented | insert, lookup, range_scan, delete, split_child (412L) |
| WAL (storage/shared/wal.spl) | Implemented | append, flush_wal, recovery_cursor, scan_from, collect_committed (119L) |
| Checkpoint ring (shared) | Implemented | persist_slot, ring_size, latest_clean (382L) |
| Intent log (shared) | Implemented | ~285L |
| DBFS Engine WAL (dbfs_engine/wal.spl) | Facade only | 13L — `type DbfsWal = SharedWal` re-export |
| DBFS Engine Recovery (recovery.spl) | Implemented | D5 5-step model: best-of-3 superblock, WAL replay, orphan discard, clean checkpoint (145L) |
| DBFS Engine Pager (pager.spl) | Implemented | Clock-sweep eviction, alloc_page, read_page, write_page, flush_dirty (224L) |
| DBFS Engine Checkpoint (checkpoint.spl) | Implemented | checkpoint_now, latest_clean, CheckpointRing integration (158L) |
| DBFS Engine Schema (schema.spl) | Implemented | Largest file — catalog schema (686L) |
| DBFS Engine Superblock (superblock.spl) | Implemented | Best-of-3 replicas, CRC (406L) |
| DBFS Engine Txn (txn.spl) | Implemented | 6-step write protocol (239L) |
| DBFS Engine MetaStore (meta_store.spl) | Implemented | 405L |
| DBFS Engine FSDriver (fs_driver.spl) | Implemented | 425L |
| DBFS Engine NsBTree (ns_btree.spl) | Implemented | DBFS-specific btree wrapper |
| DBFS Engine Arena (arena.spl) | Implemented | 167L |
| DBFS Engine RawNVMeArena | Implemented | 348L |
| SIMD Accel (db/accel.spl) | Phase 1 only | RowBitmap, VectorBatch<T>, scalar impls (664L) |
| Shared DB interface (simple_db_if/) | Partial | 130L — PageStore, WalWriter, BufferManager, RelationOracle trait stubs |
| PostgreSQL MVCC full engine | NOT implemented | Design-only; `examples/simple_db/src/engine/` does not exist |

### BTree Hardening Note

`btree.spl` implements `split_child` (line 236) and `delete_from_node` (line 317). However, **no rebalancing/merge on delete** was found: no `rebalance`, `merge`, `borrow`, `steal`, `redistribute`, `underflow`, or `fix_child` functions appear in the file. The delete walks down to the key and removes it, but underflow in internal/leaf nodes after deletion is not handled. This means the tree can become unbalanced after heavy deletions.

---

## 2. Milestone Status (M1–M5)

From `doc/05_design/simple_db_design.md`:

| Milestone | Defined Scope | Implementation Status |
|-----------|--------------|----------------------|
| **M1** | Sync engine + WAL + BRIN + pmap | **Partial** — DBFS engine exists in stdlib (not `examples/simple_db/`); WAL + checkpoint implemented; BRIN absent; pmap absent; no MVCC heap |
| **M2** | Out-of-place writes; PG wire protocol (libpq) | **Not started** — no wire protocol, no out-of-place write pipeline |
| **M3** | BRIN-HOT-logical; AIO (`nogc_async_mut`) | **Not started** — async variant mirrors sync but no BRIN/HOT logic |
| **M4** | Tiered cache; cost-model rework | **Not started** — `ml_cost_model.spl` (151L) exists as scaffold; no tiering |
| **M5** | ZNS/FDP placement | **Not started** |

**Summary:** M1 is partially implemented at the DBFS layer but the PostgreSQL-compatible relational engine (buffer pool, MVCC predicates, HOT, TOAST, BRIN index, pmap) described in the design doc does not exist anywhere in the repo.

---

## 3. Test Coverage Audit

Method: `grep -cE '^\s+it "' test/dbfs/*.spl` (correct spipe syntax).

### Spec Files with Populated `it` Blocks

| Spec File | `it` Count | Category |
|-----------|-----------|----------|
| dbfs_catalog_schema_spec.spl | 15 | Populated — cannot confirm pass/fail without running |
| bench_comparison_spec.spl | 14 | Populated |
| dbfs_capability_spec.spl | 11 | Populated |
| dbfs_fs_driver_spec.spl | 13 | Populated |
| dbfs_engine_btree_spec.spl | 8 | Populated |
| dbfs_engine_checkpoint_ring_spec.spl | 8 | Populated |
| dbfs_engine_intent_log_spec.spl | 8 | Populated |
| dbfs_engine_pager_spec.spl | 8 | Populated |
| dbfs_engine_wal_spec.spl | 8 | Populated |
| dbfs_superblock_disk_spec.spl | 8 | Populated |
| dbfs_recovery_spec.spl | 9 | Populated |
| dbfs_posix_shim_spec.spl | 9 | Populated |
| mount_table_dbfs_dispatch_spec.spl | 7 | Populated |
| dbfs_engine_checkpoint_spec.spl | 6 | Populated |
| dbfs_tx_protocol_spec.spl | 6 | Populated |
| fat32_no_regression_spec.spl | 6 | Populated |
| dbfs_no_regression_spec.spl | 5 | Populated |
| nvfs_hosted_no_regression_spec.spl | 5 | Populated |
| nvfs_no_regression_spec.spl | 8 | Populated |
| samsung_nvme_feature_policy_spec.spl | 7 | Populated |
| dbfs_driver_spec.spl | 8 | Populated |
| dbfs_ring_diag_spec.spl | 6 | Populated |
| dbfs_nvme_callback_spec.spl | 4 | Populated |
| dbfs_hw_passthrough_spec.spl | 4 | Populated |
| arena_as_blob_backend_spec.spl | 3 | Populated (2 of 3 are empty-body stubs — `it "...":` with no body before next `it`) |
| bench_harness_smoke_spec.spl | 3 | Populated |
| ramfs_open_smoke_spec.spl | 1 | Populated |

### Harness / Runner Files (Not Specs)

| File | Notes |
|------|-------|
| bench_ac7_runner.spl | Runner, no it blocks |
| bench_harness.spl | Harness library, no it blocks |
| hosted_fs_no_regression_shared.spl | Shared helpers |
| posix_baseline.spl | Baseline data |
| power_cut_harness.spl | Fault-injection harness |
| run_bench_ac7.spl | Bench runner |

### Skip/Pending/TODO

`grep -nE 'skip\(|pending\(|xit |xdescribe |TODO'` returned **no matches** across all spec files. No explicitly skipped tests found.

### Empty `it` Body Stubs

`arena_as_blob_backend_spec.spl` has 3 `it "...":` lines where at least 2 appear to be empty or near-empty bodies based on the grep output. All other specs have substantive bodies (confirmed by reading `dbfs_recovery_spec.spl`, `dbfs_engine_btree_spec.spl`, `dbfs_tx_protocol_spec.spl`).

**Note:** Test execution status (pass/fail) was not verified by running the test runner. The above categorizes specs by structural completeness only.

---

## 4. Missing Features (with Severity)

| Feature | Severity | Notes |
|---------|----------|-------|
| PostgreSQL MVCC engine (`examples/simple_db/src/`) | P0 | The entire concrete engine (buffer pool, heap pages, MVCC, HOT, BRIN, TOAST, pmap, vacuum) is unimplemented — design-only |
| PG wire protocol / libpq | P0 | M2 blocker; nothing exists |
| BTree delete rebalancing/merge | P0 | `delete_from_node` exists but no underflow handling; tree degrades after bulk deletes |
| BRIN index | P0 | M1 requirement; completely absent |
| Page map (pmap) / page-indirection | P0 | M1 requirement; absent (design describes `rel.pmap` atomic publish) |
| Out-of-place write pipeline | P1 | M2 requirement; absent |
| MVCC visibility (xmin/xmax predicates) | P0 | No heap tuple layer; no snapshot isolation in SQL engine |
| TOAST (large value storage) | P1 | Not implemented |
| HOT updates | P1 | Not implemented |
| Vacuum / dead tuple reclaim | P1 | Design references `sys_vacuum`; absent |
| Full SIMD acceleration (Phase 2+) | P2 | accel.spl is scalar only; no actual SIMD intrinsics wired |
| Tiered buffer cache | P2 | M4; `ml_cost_model.spl` is scaffold only |
| ZNS / FDP placement | P3 | M5; not started |
| AIO (async I/O path) | P2 | M3; `nogc_async_mut` mirrors exist but are not differentiated from sync |
| `simple_db_if` trait completeness | P1 | Only 130L covering PageStore, WalWriter, BufferManager, RelationOracle — Vacuumer, Checkpointer missing from interface |

---

## 5. Hardening Gaps (with Severity)

| Gap | Severity | Details |
|-----|----------|---------|
| BTree underflow on delete | P0 | No merge/rebalance in `storage/shared/btree.spl`; internal nodes can have fewer than ceil(fanout/2)-1 keys after deletions, violating B-tree invariant |
| Recovery uses module-level `var` state | P1 | `recovery.spl` stores callback state in module-level `var` globals (`_recovery_discard_cb_registered`, `_recovery_discarded_ids`, etc.); interpreter note in MEMORY.md warns module-level `var` is zero in baremetal LLVM targets (BSS clearing). Recovery state will be silently wrong in baremetal targets |
| Pager eviction fails on all-dirty | P1 | `alloc_page()` returns `Err("pager: all pages dirty; flush first")` — no background flush; caller must handle this error, but no evidence of retry/flush loop in consuming code |
| Pager is in-process only | P1 | Comment: "Simulates disk persistence for evicted pages within process lifetime." — evicted pages are lost on crash; no durable eviction path |
| WAL group-commit is in-memory only | P1 | `SharedWal.flush_wal()` increments `flush_count` and marks durable but has no actual NVMe flush call — the durability is simulated, not real |
| NVFS S4 `arena_clone_range` | P1 | Defined in NVFS contract (load-bearing P0); no implementation found in storage layer |
| NVFS S6 `atomic_pointer_record_publish` | P1 | Defined in NVFS contract; referenced in design but no implementation in storage lib |
| `simple_db_if` trait stubs are thin | P1 | At 130L the traits lack method signatures for most of the spec-described API (Vacuumer, full Checkpointer, RelationOracle range-scan, BufferManager pin/unpin) |
| No power-cut tests actually run | P2 | `power_cut_harness.spl` exists but `dbfs_recovery_spec.spl` imports it; actual hardware fault injection is simulated via `FaultDevice` struct — no real NVMe error injection |
| No integration test for full round-trip | P2 | All specs test individual layers; no end-to-end "insert → crash → recover → verify data intact" test exists |
| Checkpoint ring uses interpreter value-semantics workaround | P2 | Comment in `checkpoint.spl` line 141: "me fn mutations on self.ring are not visible (interpreter value semantics)" — workaround rather than correct fix; may behave differently in compiled mode |
| SIMD detection returns scalar | P2 | `accel_capability_report()` reports `simd_available` from `detect_profile()` but all scan functions are scalar implementations; SIMD path is never exercised |

---

## 6. NVFS Requirements Status (S1–S7)

All 7 NVFS API requirements are defined as **load-bearing P0** in `doc/05_design/nvfs/from_simple_db.md`.

| Req | Function | Status |
|-----|----------|--------|
| S1 | `arena_create(class, hint)` | Designed; `arena.spl` exists (167L) — partial |
| S2 | `arena_append_aligned(arena, bytes, granule, durability)` | Designed; `DURABLE_GROUP_COMMIT` in SharedWal is in-memory simulation only |
| S3 | `arena_seal` / `arena_discard` with generation pinning | Designed; `SealToken` in storage types; discard is callback-registered stub in recovery.spl |
| S4 | `arena_clone_range` | Designed only; no implementation found |
| S5 | `fs_caps()` / `FsCaps` struct | Designed; `nvme_feature_policy.spl` exists (capability query) — partial |
| S6 | `atomic_pointer_record_publish` | Designed; referenced in `storage/shared/__init__.spl` exports but no concrete implementation found |
| S7 | `arena_flush` / `arena_fua_append` | Designed; NVMe flush in WAL is simulated |

**Verdict:** NVFS API surface is defined in types/contracts but the NVMe-durable implementations (S2, S3, S4, S6, S7) are stubs or simulations. Real NVMe I/O path does not exist yet.

---

## 7. Recommendations (Prioritized)

### P0 — Blockers for M1

1. **Implement BTree delete rebalancing.** Add `merge_children` / `borrow_from_sibling` to `storage/shared/btree.spl`. Without this, bulk-delete workloads will corrupt tree structure and range scans will miss entries.

2. **Create `examples/simple_db/src/`** with concrete engine (buffer pool, MVCC heap, WAL writer impl, pmap). The design doc is complete; the code does not exist. M1 cannot ship without it.

3. **Implement BRIN index.** Required by M1 design; absent.

4. **Implement page-indirection map (pmap).** M1 "append-only flash" model requires `rel.pmap` + atomic publish; absent.

### P1 — Hardening Before Any Durable Storage

5. **Replace in-memory WAL flush with real NVMe flush.** `SharedWal.flush_wal()` is a counter increment. Wire `arena_flush()` / `arena_fua_append()` to an actual device path.

6. **Fix recovery module-level `var` globals** for baremetal targets. Use function-local state passed through parameters, or wrap in a struct. Module-level `var` is zero after BSS clear on LLVM targets.

7. **Add pager durability on eviction.** Evicted pages are lost on process exit. Wire eviction to `arena_append_aligned` so evicted pages persist to the WAL/data arena.

8. **Implement `arena_clone_range` (S4).** Required for checkpoint compaction and page-version cloning.

9. **Complete `simple_db_if` trait contracts.** Add `Vacuumer`, full `Checkpointer`, and `BufferManager.pin/unpin` signatures.

### P2 — Quality and Coverage

10. **Add end-to-end crash-recovery integration test.** A single spec that writes data, simulates a crash at each of the 6 D4 steps, and verifies recovery produces consistent state.

11. **Fix checkpoint ring interpreter value-semantics workaround.** The comment acknowledges the mutation is not visible in interpreter mode — this needs a structural fix before compiled-mode regression testing.

12. **Wire SIMD Phase 2.** The scalar RowBitmap and VectorBatch<T> are correct scaffolding; add actual SIMD scan kernels behind the `simd_active` capability gate.

13. **Add `arena_as_blob_backend_spec.spl` empty-body stubs.** Two of the three `it` blocks appear empty; fill them or mark the feature as not yet specified.

### P3 — Future

14. ZNS / FDP placement (M5)
15. AIO differentiation in `nogc_async_mut` variant (M3)
16. Tiered buffer cache and ML cost model (M4)
17. PG wire protocol / libpq (M2)

---

## Appendix: Key File Paths

- Design doc: `doc/05_design/simple_db_design.md`
- NVFS requirements: `doc/05_design/nvfs/from_simple_db.md`
- SIMD design: `doc/05_design/simple_db_shared_accel_simd.md`
- Shared storage: `src/lib/nogc_sync_mut/storage/shared/{btree,wal,checkpoint_ring,intent_log}.spl`
- DBFS engine (sync): `src/lib/nogc_sync_mut/db/dbfs_engine/`
- DBFS engine (async): `src/lib/nogc_async_mut/db/dbfs_engine/`
- SIMD accel: `src/lib/nogc_sync_mut/db/accel.spl`
- Shared DB interface: `src/lib/nogc_sync_mut/simple_db_if/`
- Test specs: `test/dbfs/*.spl`
- Full engine submodule (empty): `examples/simple_db/`
