# Simple DB Accel Remains — 2026-05-02

> Status: PARTIAL — Phase 1 + Phase 2 landed; Phase 3 (ML/planner) TODO

## Done — Phase 1 landed

- shared `std.db.accel` module with bitmap, batch, text, trigram, and key-scan
  helpers (`src/lib/nogc_sync_mut/db/accel.spl`)
- SDN query batching and `filter_in` OR semantics
- DBFS dentry summary-hash and prefix scan helpers
- spostgre BRIN-aware scan and minimal text-search prototype
- targeted regression tests for all three consumers

## Done — Phase 2 index structures landed (2026-05-20)

- reusable prefix/radix index replacing DBFS summary-hash scan helpers for
  repeated namespace scans: `src/lib/nogc_sync_mut/db/prefix_index.spl`
  — `PrefixIndex`, `prefix_index_new/insert/sort/lookup_prefix/lookup_exact/size`
- spostgre in-memory prefix+text index layered above trigram candidate extraction:
  `src/lib/nogc_sync_mut/db/text_index.spl`
  — `TextIndex`, `text_index_new/insert/search_prefix/search_contains/search_exact`
- reusable page-header summary scan helpers compatible with BRIN-style range
  elimination: `src/lib/nogc_sync_mut/db/page_summary.spl`
  — `PageSummary`, `PageSummaryIndex`, scan/filter helpers
- OR-semantics batch filter_in helper over shared accel:
  `src/lib/nogc_sync_mut/db/filter_in.spl`
  — `FilterInResult`, `filter_in_text/filter_in_int` and count helpers
- regression spec covering all four: `test/perf/bench/db_accel_index/db_accel_index_spec.spl`

## Research — Phase 3 planner / ML work (TODO)

- learned indexes for static sorted segments
- learned cardinality estimation for spostgre planning
- worst-case-optimal join applicability for Simple DB workloads
- SIMD-backed posting-list execution and full inverted-index design

## Risks

- Phase 1 reports real SIMD capability but still uses scalar kernels; perf
  uplift today comes from batching/bitmap materialization more than ISA-specific
  intrinsics
- Current benchmark evidence in `test/perf/bench/simple_db_shared_accel.spl`
  shows the shared path is still slower than direct scalar baselines on the
  2026-05-02 host run; further optimization is required before calling this a
  performance win
- `summary_text_hash` is intentionally a cheap prefilter hash; correctness
  depends on the exact-match refinement step staying in place
- spostgre scan integration is additive utility code because the engine is still
  skeletal; broader executor wiring should wait for the engine’s execution path
  to stabilize

## Blockers

- benchmark script exists at `test/perf/bench/simple_db_shared_accel.spl`, but
  the current evidence still reflects scalar-fallback kernels rather than
  ISA-specific SIMD speedups
- startup/RSS evidence is now report-driven rather than enforced by a dedicated
  spec gate
- no planner/executor surface in spostgre yet exists to consume the new scan
  helpers end-to-end
