<!-- codex-design -->
# Simple DB Shared Accel SIMD

## Intent

Implement a shared Phase 1 acceleration layer for Simple DB consumers without
rewriting planner or storage contracts. The landed code prioritizes reusable
scan primitives:

- `RowBitmap` with `and_with`, `or_with`, `and_not`, `count`, and density
- `VectorBatch<T>` with one shared default batch size
- text helpers for equality, prefix, suffix, substring, token, and trigram work
- fixed-width key span scans
- capability reporting backed by `std.simd`

## Public Surface

`src/lib/nogc_sync_mut/db/accel.spl` exports:

- `DB_ACCEL_DEFAULT_BATCH_SIZE`
- `KeySpan`, `ByteSpan`, `TextSpan`, `VectorBatch<T>`
- `RowBitmap`
- `ScanPredicateKind`, `ScanPredicate`
- `FilterStats`
- `AccelCapabilityReport`
- helpers such as `scan_key_span`, `scan_text_values`,
  `text_contains_token`, `trigram_extract`, and `summary_text_hash`

`AccelCapabilityReport` now distinguishes:

- `simd_available` — host/runtime tier supports a SIMD target
- `simd_active` — a DB accel kernel is currently using that SIMD path

Phase 1 intentionally reports `simd_active = false` because the exported DB
scan kernels are still scalar fallbacks.

## Consumer Wiring

### SDN query builder

- `QueryBuilder.execute()` now computes one candidate bitmap and materializes
  rows after filtering instead of chaining `results.filter(...)`.
- `filter_in()` now has OR semantics via `CompareOp.InSet`.
- `Eq`, `Contains`, `StartsWith`, and `EndsWith` use shared accel text helpers.

### DBFS schema scans

- `DentryTable.find_child_accel(parent_ino, name)` uses shared summary-hash
  filtering before exact name comparison.
- `DentryTable.list_children_with_prefix(parent_ino, prefix)` uses shared
  prefix helpers plus bitmap materialization.
- Collision safety is preserved by exact-name refinement after the hash pass.

### spostgre

- `examples/spostgre/src/engine/scan.spl` adds a BRIN-aware tuple scan helper.
- `spostgre_scan_text_with_brin()` keeps BRIN as the coarse filter and refines
  surviving tuples with shared text scans.
- `spostgre_text_search()` is the minimal text-search prototype: token match
  first, trigram overlap fallback second.

## Verification Notes

- Shared accel unit tests cover bitmap logic, text predicates, scalar scan
  parity expectations, and capability reporting.
- SDN integration tests cover `filter_in` OR semantics and prefix/suffix scans.
- DBFS integration tests cover prefix scans plus summary-hash collision safety.
- spostgre unit tests cover plain batched scan, BRIN-assisted refinement, and
  token/trigram search candidates.
- `test/perf/bench/simple_db_shared_accel.spl` records current perf evidence.
  On the 2026-05-02 host run, the shared accel path remained slower than direct
  scalar baselines, so Phase 1 should be treated as API/consolidation work, not
  a measured throughput win yet.
- Perf baseline script: `test/perf/bench/simple_db_shared_accel.spl`
- Perf evidence: `doc/09_report/verify/simple_db_shared_accel_perf_2026-05-02.md`

## Deferred

Tracked separately in `doc/08_tracking/feature_request/simple_db_requests.md`:

- ART / SP-GiST-like prefix indexes
- learned indexes for static sorted segments
- learned cardinality estimation
- vectorized posting-list execution
- worst-case-optimal join follow-up
