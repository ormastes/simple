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
- **Status:** Open
- **Requested-semantics:**
  Add a reusable in-memory prefix/radix index above the Phase 1 bitmap scans so
  repeated `StartsWith` and hierarchical-key lookups do not rescan full row or
  dentry arrays.
- **Acceptance-criteria:**
  - reusable across SDN query paths, DBFS namespace paths, and spostgre text/key scans
  - supports exact, prefix, and range-like descendant lookups
  - retains scalar fallback and host capability reporting
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none

### FR-SIMPLE-DB-0002 — Add learned index support for static sorted segments

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** simple-db
- **Priority:** P2
- **Status:** Open
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

### FR-SIMPLE-DB-0003 — Add learned cardinality estimation for spostgre planning

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** spostgre
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  Once spostgre has a real planner path, add a learned cardinality-estimation
  experiment that can coexist with BRIN summaries and conventional statistics.
- **Acceptance-criteria:**
  - isolated behind a planner experiment flag
  - records estimation error against real scan counts
  - does not alter execution correctness when disabled
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none

### FR-SIMPLE-DB-0004 — Add vectorized posting-list / inverted-index execution

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** simple-db
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:**
  Extend the shared text-search work from token/trigram candidate extraction into
  actual posting-list intersection and bitmap materialization for repeated text
  search workloads.
- **Acceptance-criteria:**
  - shared posting-list bitmap primitives reused by SDN/spostgre consumers
  - supports token AND/OR evaluation without row-at-a-time loops
  - benchmark evidence for latency and RSS
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none

### FR-SIMPLE-DB-0005 — Research worst-case-optimal joins for Simple DB workloads

- **Filed-on:** 2026-05-02
- **Filed-by:** Codex
- **Target:** simple-db
- **Priority:** P2
- **Status:** Open
- **Requested-semantics:**
  Evaluate whether worst-case-optimal joins fit the eventual spostgre planner or
  any shared relational layer, rather than forcing that complexity into Phase 1.
- **Acceptance-criteria:**
  - research note compares representative workloads against current nested/scan plans
  - identifies storage/layout prerequisites before implementation
  - results in either a scoped design doc or an explicit rejection rationale
- **Related-upfront:** none
- **Related-design-doc:** `doc/05_design/simple_db_shared_accel_simd.md`
- **Related-issue:** none
