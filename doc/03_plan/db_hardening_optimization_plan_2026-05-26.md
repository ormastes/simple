# Database Hardening And Optimization Plan - 2026-05-26

## Purpose

Consolidate SimpleQ, embedded Simple DB, full Simple DB, DBFS-backed storage,
BM25/FTS5 search, logging, and executor/index optimization into one database
track.

## Source Plans

- `doc/03_plan/crash_recovery_replan_2026-05-25.md`
- `doc/03_plan/active_goal_restart_sqlite_search_log_2026-05-24.md`
- `doc/03_plan/agent_tasks/simple_db_accel_remains_2026-05-02.md`
- `doc/03_plan/nvfs_dbfs_real_filesystem.md`
- `doc/03_plan/sys_test/simple_db_nvfs_constants.md`
- `doc/05_design/simple_db_design.md`
- `doc/05_design/unified_database_design.md`
- `doc/05_design/database_access_enforcement_design.md`
- `doc/04_architecture/dbfs_architecture.md`

## Scope

- Harden embedded DB correctness:
  - SDN atomic I/O
  - durable reopen behavior
  - update/delete visibility in FTS/BM25
  - cache invalidation after insert/update/delete/drop
  - no stale index reads after reopen.
- Optimize embedded DB:
  - prefix/text/page-summary helpers in the real executor path
  - row-level `MATCH`/`fts_match`
  - BM25/FTS5 facade through shared FTS engine
  - planner hooks for prefix, contains, exact, and page-summary scans.
- Improve SimpleQ as DB substrate:
  - bounded queue backpressure
  - batch push/pop APIs
  - optional DBFS durable handoff.
- Improve full Simple DB in `examples/simple_db/`:
  - WAL, TOAST, and buffer-pool benchmarks over NVFS/DBFS storage paths
  - comparison against embedded DB and direct DBFS/NVFS baselines.
- Keep logging/progress options stable for DB tools without flooding logs.

## Crash-Safe Execution Rules

- DB benchmarks must be bounded and must not run in parallel with QEMU,
  board serial capture, full bootstrap, or webserver load tests.
- Use isolated temp DB roots for destructive tests.
- Record dataset size, row count, index count, and storage provider for every
  benchmark.
- Stop on disk-free floor below 250 GiB or available memory below 32 GiB.

## Work Queue

1. Audit current pure DB/BM25/FTS5 implementation and tests from the active
   restart plan.
2. Remove temporary debug files and stale scalar-only benchmark assumptions.
3. Wire shared DB accel helpers into the actual executor path, not only utility
   tests.
4. Add benchmark gates for:
   - point lookup
   - prefix search
   - contains search
   - BM25/FTS5 query
   - update/delete index invalidation
   - reopen/recovery.
5. Add SimpleQ batch/backpressure APIs and DBFS durable handoff coverage.
6. Refresh full Simple DB benchmark against DBFS/NVFS and optimized FAT.

## Verification Gates

- Focused DBFS and pure DB specs pass before performance claims.
- No benchmark may claim speedup without a scalar/direct baseline in the same
  report.
- Every REQ or plan claim for durability has a reopen or recovery test.
- Every index/cache optimization has update/delete/drop invalidation coverage.
- Full DB and embedded DB reports must distinguish correctness, cold-start,
  warm-cache, and post-reopen behavior.
