# Simple DB Accel Remains — 2026-05-02

## Do Now — Phase 1 landed

- shared `std.db.accel` module with bitmap, batch, text, trigram, and key-scan
  helpers
- SDN query batching and `filter_in` OR semantics
- DBFS dentry summary-hash and prefix scan helpers
- spostgre BRIN-aware scan and minimal text-search prototype
- targeted regression tests for all three consumers

## Next — Phase 2 index structures

- replace DBFS summary-hash scan helpers with stronger reusable prefix/radix
  index structures where repeated namespace scans justify persistent indexing
- add a spostgre in-memory prefix/text index layered above the current trigram
  candidate extraction
- extend shared accel with reusable page-header summary scan helpers once the
  page metadata layout is consolidated

## Research — Phase 3 planner / ML work

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
