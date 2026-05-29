# Simple DB — Test Coverage & Feature Request Audit

> Generated: 2026-05-23
> Scope: test/dbfs/, test/system/db_*, test/perf/bench/simple_db_*, test/unit/lib/*/simple_db_if/, doc/05_design/*, doc/08_tracking/feature_request/simple_db_requests.md

---

## 1. Test Inventory

### 1.1 DBFS Tests (`test/dbfs/` — 33 files, 28 spec files)

| File | `it` blocks | `expect`/`assert` | Status |
|------|-------------|-------------------|--------|
| arena_as_blob_backend_spec.spl | 3 | 13 | Real |
| bench_comparison_spec.spl | 14 | 15 | Real (benchmark) |
| bench_harness_smoke_spec.spl | 3 | 4 | Real |
| dbfs_capability_spec.spl | 11 | 11 | Real |
| dbfs_catalog_schema_spec.spl | 15 | 16 | Real |
| dbfs_driver_spec.spl | 8 | 9 | Real |
| dbfs_engine_btree_spec.spl | 8 | 10 | Real |
| dbfs_engine_checkpoint_ring_spec.spl | 8 | 12 | Real |
| dbfs_engine_checkpoint_spec.spl | 6 | 6 | Real |
| dbfs_engine_intent_log_spec.spl | 8 | 15 | Real |
| dbfs_engine_pager_spec.spl | 8 | 8 | Real |
| dbfs_engine_wal_spec.spl | 8 | 8 | Real |
| dbfs_fs_driver_spec.spl | 13 | 16 | Real |
| dbfs_hw_passthrough_spec.spl | 5 | 9 | Real |
| dbfs_no_regression_spec.spl | 5 | 10 | Real |
| dbfs_nvme_callback_spec.spl | 4 | 25 | Real |
| dbfs_posix_shim_spec.spl | 9 | 10 | Real |
| dbfs_recovery_spec.spl | 9 | 10 | Real |
| dbfs_ring_diag_spec.spl | 8 | 6 | Real |
| dbfs_superblock_disk_spec.spl | 8 | 18 | Real |
| dbfs_tx_protocol_spec.spl | 6 | 6 | Real |
| fat32_no_regression_spec.spl | 6 | 12 | Real |
| mount_table_dbfs_dispatch_spec.spl | 8 | 7 | Real |
| nvfs_hosted_no_regression_spec.spl | 5 | 10 | Real |
| nvfs_no_regression_spec.spl | 8 | 14 | Real |
| ramfs_open_smoke_spec.spl | 1 | 1 | Real (smoke) |
| samsung_nvme_feature_policy_spec.spl | 7 | 20 | Real |
| bench_harness.spl | 1 | 0 | Harness only (no assertions) |
| bench_ac7_runner.spl | 0 | 0 | Runner script (no it blocks) |
| hosted_fs_no_regression_shared.spl | 0 | 11 | Shared helper (no it blocks; assertions in helpers) |
| posix_baseline.spl | 0 | 0 | Baseline helper only |
| power_cut_harness.spl | 0 | 0 | Harness only |
| run_bench_ac7.spl | 0 | 0 | Runner script |

**Total DBFS:** ~204 `it` blocks; ~296 assertions across 27 active spec files.
**Skip/TODO/stub occurrences in dbfs (non-spipe files):** 14 lines — none are empty `it` stubs; all are meaningful uses (`pending` checkpoint state, "skips replica with invalid CRC" test name, fat32_stub imports, harness comments).
**Verdict:** DBFS suite is substantively real. No hollow stubs detected.

---

### 1.2 System Tests

| File | `it` blocks | assertions | Status |
|------|-------------|------------|--------|
| test/system/db_sdn_spec.spl | 3 | 10 | Real — covers SDN table import/export, @cover annotation targets `src/lib/nogc_sync_mut/database/sdn_table.spl` at 60% |
| test/system/simple_db_nvfs_constants_spec.spl | 1 | 4 | Real — nvfs constant validation |

---

### 1.3 Unit Tests (`test/unit/lib/*/simple_db_if/`)

| File | `it` blocks | assertions | Status |
|------|-------------|------------|--------|
| gc_async_mut/simple_db_if/simple_db_if_facade_spec.spl | 1 | 7 | Real |
| nogc_async_mut/simple_db_if/simple_db_if_facade_spec.spl | 1 | 7 | Real |

**Note:** Only 2 active unit spec files for simple_db_if (one per allocator variant). Coverage is thin — 1 `it` block each, 7 assertions. These are smoke-level only.

---

### 1.4 Perf Benchmarks (`test/perf/bench/simple_db_*.spl`)

| File | Status | Notes |
|------|--------|-------|
| simple_db_wal_append.spl | Real (CPU/framing only) | Scenarios W1–W3: 1000× wal_append, 100× commit_group, 10× recover_tail. Explicitly disclaimed: in-process nvfs_shim only, NOT real NVMe. Real durability benchmarks require Phase 10+ (NVMe FUA path). |
| simple_db_shared_accel.spl | Real (scalar fallback) | Measures BRIN-aware scan, SDN, DBFS hot paths. Capability report is real but kernels are still scalar. Accel doc notes shared path is still slower than direct scalar on 2026-05-02 host run. |

**Verdict:** Both benchmarks are functional but reflect in-process / scalar-fallback costs, not production hardware numbers. They are useful CPU-cost baselines, not performance guarantees.

---

## 2. Feature Requests Status

Source: `doc/08_tracking/feature_request/simple_db_requests.md`

| ID | Title | Priority | Status |
|----|-------|----------|--------|
| FR-SIMPLE-DB-0001 | ART / SP-GiST-like prefix index for text and hierarchical keys | P2 | Open |
| FR-SIMPLE-DB-0002 | Learned index support for static sorted segments | P2 | Open |
| FR-SIMPLE-DB-0003 | Learned cardinality estimation for Simple DB planning | P2 | Open |
| FR-SIMPLE-DB-0004 | Vectorized posting-list / inverted-index execution | P1 | Open |
| FR-SIMPLE-DB-0005 | Research worst-case-optimal joins for Simple DB workloads | P2 | Open |

**All 5 requests are Open.** No closed or in-progress markers.

**Relationship to accel work:**
- FR-0001 (prefix index): Phase 2 landed a `PrefixIndex` / `TextIndex` implementation. FR-0001 may be partially addressed — but the FR itself is not marked closed. Gap: SP-GiST-style hierarchical key support is not mentioned as shipped.
- FR-0002 / FR-0003 / FR-0005: Explicitly listed as Phase 3 TODO in `doc/03_plan/agent_tasks/simple_db_accel_remains_2026-05-02.md`.
- FR-0004 (vectorized posting-list): Phase 2 landed `filter_in` with OR semantics and trigram candidate extraction; full inverted-index design listed as Phase 3 TODO.

---

## 3. Hardening Design Docs Status

### 3.1 Web DB Primitive Hardening (`doc/05_design/web_db_primitive_hardening.md`)

| Area | What's Planned | Implementation Status |
|------|---------------|----------------------|
| Web (Channel) | Add `closed: bool` to `BoundedChannel<T>`; `close()`, `is_closed()`, `try_send()` returning `Err(OverflowError)` after close | **Designed only** — no implementation evidence found in test suite |
| HTTP/Web Framework | Replace placeholder branch bodies with `continue`/`return`/response sending; handle `ConnectionAction.WriteResponse` and `ConnectionAction.SendFile` explicitly in worker completion paths | **Designed only** — "placeholder" language confirms not implemented |
| Database | (section present) | Content not resolved to specific items in search; see doc for details |
| Primitive | (section present) | Content not resolved to specific items in search; see doc for details |

**Verdict: Designed, not implemented.** The hardening doc uses "placeholder" and prescriptive "replace" language throughout, indicating this is a to-do design, not a completed implementation. No corresponding test coverage found.

### 3.2 Database Access Enforcement Design (`doc/05_design/database_access_enforcement_design.md`)

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 1: Lint Rule | Quick win lint enforcement | **Designed** |
| Phase 2: Unified Library | Extend `lib.database`; migrate test runner and feature_db; delete ~500 lines duplication | **Designed** — unit tests claim 27/27 passing for core operations, atomic writes, locking (marked ✅ in doc) |
| Phase 3: Module Access Control | Privacy enforcement via module access control or capability-based access | **Designed** — depends on module privacy language feature (not yet confirmed available) |

**Verdict: Phase 1 and Phase 2 unit-test layer appear designed and partially implemented** (27 tests claimed passing for `test/lib/database_spec.spl`). Integration and end-to-end tests listed as "Needed." Phase 3 is blocked on a language feature.

### 3.3 Database Synchronization Implementation (`doc/05_design/database_synchronization_implementation.md`)

| Phase | Description | Status |
|-------|-------------|--------|
| Phase 1: Atomic Writes (MVP) | `file_atomic_write` pattern for todo_db, feature_db, task_db | **Designed with Rust code samples** — impl guide format |
| Phase 2: File Locking | `db_lock.rs` advisory lock module | **Designed** |
| Phase 3: Unified Database Module | `unified_db.rs` generic Record trait | **Designed** |
| Phase 4: Versioning & Conflict Resolution | `version` + `last_modified` fields, conflict resolution | **Designed** |

**Verdict: Design only.** The doc provides full Rust implementation blueprints but these are guides for implementation, not evidence of completion. No corresponding `.spl` tests found for sync behavior.

---

## 4. Accel Remaining Work (`doc/03_plan/agent_tasks/simple_db_accel_remains_2026-05-02.md`)

- **Phase 1 (Done):** `std.db.accel` — bitmap, batch, text, trigram, key-scan; SDN batching; DBFS summary-hash; BRIN-aware scan.
- **Phase 2 (Done — 2026-05-20):** `PrefixIndex`, `TextIndex`, `PageSummary`/`PageSummaryIndex`, `filter_in` with OR semantics; regression spec at `test/perf/bench/db_accel_index/db_accel_index_spec.spl`.
- **Phase 3 (TODO):** Learned indexes, learned cardinality estimation, worst-case-optimal joins, SIMD-backed inverted-index.
- **Blockers:** No planner/executor surface in Simple DB yet to consume scan helpers end-to-end; benchmark evidence is scalar-fallback only; startup/RSS not gate-enforced.
- **Risk:** Shared accel path benchmarks slower than direct scalar on 2026-05-02; further optimization required before claiming a perf win.

---

## 5. Coverage Gaps

| Gap | Area | Severity | Rationale |
|-----|------|----------|-----------|
| G1 | WAL durability on real NVMe / FUA path | P0 | `simple_db_wal_append.spl` is explicitly in-process only; real durability untested until Phase 10+ |
| G2 | `BoundedChannel` close/try_send hardening | P0 | Designed but no implementation or test; affects backpressure correctness in web DB path |
| G3 | HTTP worker `ConnectionAction` completion paths | P0 | Described as "placeholder" in hardening doc; incomplete handler = silent data loss |
| G4 | Database sync (atomic writes, file locking) | P1 | 4-phase sync guide is design-only; no `.spl` tests confirm atomic write behavior |
| G5 | simple_db_if unit coverage (only 1 `it` each variant) | P1 | Facade-level smoke only; no error path, concurrency, or multi-op tests |
| G6 | SDN table 60% coverage | P1 | `@cover` annotation on `db_sdn_spec.spl` targets 60%; 40% of sdn_table.spl is untested |
| G7 | Access enforcement (Phase 2 integration + E2E tests) | P1 | Doc lists integration and E2E as "Needed"; only unit-layer claimed passing |
| G8 | FR-0004 vectorized posting-list / inverted index | P1 | Highest-priority open FR; Phase 3 TODO, no test coverage |
| G9 | Phase 3 ML/planner work (FR-0002, FR-0003, FR-0005) | P2 | All open FRs; explicit research TODO; no design doc yet |
| G10 | Shared accel performance regression gate | P2 | Shared path slower than scalar on 2026-05-02 run; no spec gate enforces perf bounds |
| G11 | Module access control / capability enforcement (Phase 3) | P2 | Blocked on language module privacy feature; no timeline |
| G12 | Power-cut / crash recovery integration | P2 | `power_cut_harness.spl` has 0 `it` blocks; harness exists but no spec exercises it |

---

## 6. Recommendations (Prioritized)

### P0 — Fix immediately

1. **Implement `BoundedChannel` close semantics** and add a `dbfs_channel_close_spec.spl` test covering `is_closed()` and `try_send()` after close. This unblocks the web DB backpressure story.
2. **Implement `ConnectionAction.WriteResponse` / `SendFile`** handler in HTTP worker completion path. Add a round-trip integration test. Current placeholder = silent data loss risk.
3. **Gate WAL durability on a real FUA path spec** (even a mock NVMe block device) before Phase 10 to avoid the "green CI, broken on hardware" trap. Mark current wal_append benchmark clearly as CPU-only in test metadata.

### P1 — Address in current sprint

4. **Implement Phase 1 atomic writes** (`file_atomic_write`) in Simple language per sync design doc. Add at least 3 `it` blocks: write succeeds, write is atomic on crash (temp-file rename pattern), concurrent write serialization.
5. **Expand simple_db_if unit tests** from 1 to ≥ 5 `it` blocks per variant: error path, concurrent access, multi-op sequence, null/empty key, oversized value.
6. **Increase SDN table coverage** from 60% to ≥ 85%: identify uncovered paths via `bin/simple doc-coverage --missing` and add targeted `it` blocks to `db_sdn_spec.spl`.
7. **Add access enforcement integration tests** as specified in Phase 2 of `database_access_enforcement_design.md` (test run management, feature status updates, stale run cleanup).
8. **Activate `power_cut_harness.spl`** — add at least 3 crash-recovery `it` blocks that use the existing harness infrastructure.

### P2 — Plan for next sprint

9. **Close or update FR-SIMPLE-DB-0001** — Phase 2 landed `PrefixIndex`/`TextIndex`; evaluate whether SP-GiST hierarchical key support is met and mark FR closed or add remaining ACs.
10. **Add a perf regression gate spec** that compares shared-accel path against scalar baseline and fails if shared path regresses more than 20%. Currently benchmarks are informational only.
11. **Scope FR-0004 (vectorized posting-list)** into a Phase 3 design doc before implementation.
12. **Unblock Phase 3 access enforcement** by filing a concrete language feature request for module privacy, or pivot to the capability-based approach (Strategy 3) which does not require it.
