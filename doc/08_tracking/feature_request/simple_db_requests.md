# Simple DB Feature Requests

Secondary channel for shared acceleration follow-ups discovered while landing
the Phase 1 scan/bitmap tranche.

- **Target:** simple-db
- **Owning design docs:**
  - `doc/05_design/simple_db_shared_accel_simd.md`
  - `doc/04_architecture/simple_db_shared_accel_simd.md`

## Open Requests

### FR-SIMPLE-DB-0001 — Add ART / SP-GiST-like prefix index for text and hierarchical keys

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** simple-db
- **Priority:** P1
- **Status:** Implemented (2026-05-29)
- **Requested-semantics:**
  Add a reusable in-memory prefix/radix index above the Phase 1 bitmap scans so
  repeated `StartsWith` and hierarchical-key lookups do not rescan full row or
  dentry arrays.
- **Acceptance-criteria:**
  - [x] reusable across SDN query paths, DBFS namespace paths, and Simple DB text/key scans
  - [x] supports exact, prefix, and range-like descendant lookups
  - [x] retains scalar fallback and host capability reporting
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none
- **Progress 2026-05-29:** `std.db.prefix_index` now normalizes lookups through
  sorted index ranges, exposes `prefix_index_prefix_range(...)` and
  `prefix_index_lookup_descendants(...)`, and `DbTable` rebuilds store a sorted
  key index. Focused regression coverage:
  `test/unit/lib/db/prefix_index_spec.spl`.
- **Progress 2026-05-29:** DBFS `DentryTable` now maintains the shared prefix
  index for exact child lookups and parent-scoped prefix listings, with stale
  row-position protection after removal. Focused regression coverage:
  `test/unit/lib/db/dbfs_dentry_prefix_index_spec.spl` plus
  `test/integration/storage/dbfs/dbfs_catalog_schema_spec.spl`.
- **Progress 2026-05-29:** SDN `QueryBuilder` now routes single-filter
  `CompareOp.StartsWith` scans through `std.db.prefix_index` and restores row
  order before returning unsorted query results. Focused regression coverage:
  `test/unit/lib/database/database_query_spec.spl` plus
  `test/system/database/database_system_spec.spl`.
- **Progress 2026-05-29:** Sync and async SDN `QueryBuilder` now keep a
  per-builder prefix-index cache keyed by field, so repeated `StartsWith`
  executions on the same query builder reuse the sorted field index instead of
  rebuilding it. Regression coverage asserts the build counter remains stable
  across repeated executions.
- **Progress 2026-05-29:** Representative shared-accel benchmark evidence was
  refreshed in `test/perf/bench/simple_db_shared_accel.spl`. The interpreter
  run reports SDN cached repeated prefix p50 `11929530ns` / p99 `13532417ns`
  versus rebuild-each-query p50 `651859937ns` / p99 `664099899ns`, with
  `/usr/bin/time` max RSS `59208KB`. The same run includes preflight checks for
  text, SDN, DBFS, Simple DB BRIN refine, and repeated-prefix cache reuse.

### FR-SIMPLE-DB-0002 — Add learned index support for static sorted segments

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** simple-db
- **Priority:** P2
- **Status:** Implemented (2026-05-29)
- **Requested-semantics:**
  For append-mostly or sealed sorted segments, add a learned-index experiment
  layer that can map probe keys to narrow candidate windows before exact scan.
- **Acceptance-criteria:**
  - explicit opt-in only
  - fallback to exact segment scan when model bounds are unsafe
  - benchmarked against bitmap-only Phase 1 scans
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none
- **Progress 2026-05-29:** Added pure Simple
  `std.db.learned_index` for sealed/static sorted numeric segments. The
  experiment is explicit opt-in via `learned_segment_build(..., true)`,
  disables itself for unsafe empty/mismatched/unsorted input, and exact-checks
  every predicted candidate window before returning row IDs. Unsafe or disabled
  probes fall back to full exact segment scans. Focused coverage:
  `test/unit/lib/db/learned_index_spec.spl`.
- **Progress 2026-05-29:** `test/perf/bench/simple_db_shared_accel.spl` now
  benchmarks the opt-in learned exact lookup against scalar exact scan and
  bitmap-only exact scan. Fresh interpreter evidence: learned p50 `24037ns` /
  p99 `46279ns`; scalar exact p50 `1987919ns` / p99 `2190348ns`; bitmap-only
  exact p50 `2397347ns` / p99 `2743794ns`.

### FR-SIMPLE-DB-0003 — Add learned cardinality estimation for Simple DB planning

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** Simple DB
- **Priority:** P2
- **Status:** Implemented (2026-05-29)
- **Requested-semantics:**
  Once Simple DB has a real planner path, add a learned cardinality-estimation
  experiment that can coexist with BRIN summaries and conventional statistics.
- **Acceptance-criteria:**
  - isolated behind a planner experiment flag
  - records estimation error against real scan counts
  - does not alter execution correctness when disabled
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none
- **Progress 2026-05-29:** Added pure Simple
  `std.db.cardinality_estimator` as an opt-in planner experiment. Disabled
  estimators return the conventional estimate and are not wired into automatic
  execution. Opted-in estimators can choose learned observations, BRIN candidate
  counts, or conventional estimates, and `learned_cardinality_record(...)`
  records absolute estimation error against exact scan counts. Focused coverage:
  `test/unit/lib/db/cardinality_estimator_spec.spl`.

### FR-SIMPLE-DB-0004 — Add vectorized posting-list / inverted-index execution

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** simple-db
- **Priority:** P1
- **Status:** Implemented (2026-05-29)
- **Requested-semantics:**
  Extend the shared text-search work from token/trigram candidate extraction into
  actual posting-list intersection and bitmap materialization for repeated text
  search workloads.
- **Acceptance-criteria:**
  - shared posting-list bitmap primitives reused by SDN/Simple DB consumers
  - supports token AND/OR evaluation without row-at-a-time loops
  - benchmark evidence for latency and RSS
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none
- **Progress 2026-05-29:** Added shared posting-list bitmap primitives to
  `std.db.accel`: `PostingList`, `PostingBitmapResult`,
  `posting_list_to_bitmap(...)`, `posting_lists_and_bitmap(...)`, and
  `posting_lists_or_bitmap(...)`. Token AND/OR evaluation now materializes
  posting lists into `RowBitmap` union/intersection without rescanning every
  row. Focused coverage: `test/unit/lib/db/posting_list_bitmap_spec.spl`.
- **Progress 2026-05-29:** `test/perf/bench/simple_db_shared_accel.spl` now
  includes posting-list AND/OR bitmap cases plus scalar full-scan baselines.
  Fresh interpreter evidence: AND bitmap p50 `11633893ns` / p99 `12447263ns`
  versus scalar AND p50 `3192243ns` / p99 `3327572ns`; OR bitmap p50
  `27111447ns` / p99 `29883254ns` versus scalar OR p50 `4197560ns` / p99
  `4410038ns`; `/usr/bin/time` max RSS `61424KB`, elapsed `0:56.44`.
  Current implementation is scalar fallback and correctness/shape evidence,
  not a claim of speedup over small synthetic full scans.

### FR-SIMPLE-DB-0005 — Research worst-case-optimal joins for Simple DB workloads

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** simple-db
- **Priority:** P2
- **Status:** Implemented (research decision, 2026-05-29)
- **Requested-semantics:**
  Evaluate whether worst-case-optimal joins fit the eventual Simple DB planner or
  any shared relational layer, rather than forcing that complexity into Phase 1.
- **Acceptance-criteria:**
  - research note compares representative workloads against current nested/scan plans
  - identifies storage/layout prerequisites before implementation
  - results in either a scoped design doc or an explicit rejection rationale
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_wco_joins.md`
- **Related-issue:** none
- **Progress 2026-05-29:** Completed research in
  `doc/01_research/local/simple_db_wco_joins_2026-05-29.md`. Current Simple DB
  workloads are unary lookup/filter, DBFS namespace lookup, SDN filter chains,
  posting-list token set operations, and BRIN refine; none require WCO joins
  yet. The design decision in `doc/05_design/simple_db_wco_joins.md` defers
  implementation until Simple DB has a multi-relation query model, sorted
  keyset iterators, multi-attribute indexes, and cyclic/high-fanout workload
  fixtures.
