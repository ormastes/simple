# SStack State: db-hardening-optimizer-general

## User Request
> DB hardening: wire prefix_index/text_index/page_summary/filter_in/query_planner into DbTable executor path with cache invalidation on insert/update/delete, and generalize app/optimize CLI to support DB query optimization analysis alongside MIR passes

## Task Type
feature

## Refined Goal
> Wire the existing but isolated Phase 2 DB acceleration modules (prefix_index, text_index, page_summary, filter_in) and Phase 3 query planner into the DbTable executor path so queries use indexed lookups instead of linear scans. Add cache/index invalidation on every mutation (insert, update, delete). Generalize the `app/optimize` CLI to analyze DB query patterns alongside MIR optimization passes, making it a general-purpose optimization tool rather than MIR-only.

## Acceptance Criteria
- [x] AC-1: DbTable maintains a PrefixIndex and TextIndex; insert/delete/update automatically update both indexes
- [x] AC-2: db_query functions (db_prefix_scan, db_range_scan, db_keys_matching) use indexes when available instead of linear scan
- [x] AC-3: Cache invalidation: after insert/update/delete, stale index entries are removed and re-added; no stale reads possible
- [x] AC-4: Query planner (choose_plan) is called by db_query to select FullScan vs IndexLookup/IndexPrefix based on available indexes
- [x] AC-5: `app/optimize` CLI accepts `--db-analyze` flag to analyze DB query patterns (prefix/contains/exact usage) alongside existing MIR analysis
- [x] AC-6: Spec coverage: db_hardening_optimizer_spec.spl tests index maintenance on insert/delete, cache invalidation, planner integration, and optimizer CLI db-analyze mode
- [x] AC-7: All existing DB tests continue to pass (no regressions)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-26
- [x] 2-research (Analyst) — 2026-05-26 (inline, modules already existed)
- [x] 3-arch (Architect) — 2026-05-26 (inline, wiring pattern 1: DbTable owns indexes)
- [x] 4-spec (QA Lead) — 2026-05-26
- [x] 5-implement (Engineer) — 2026-05-26
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Phase Outputs

### 1-dev
**Task type:** feature
**Refined goal:** Wire isolated DB accel modules into executor path with index maintenance + cache invalidation on mutations. Generalize app/optimize for DB query analysis.

**Key findings from orientation:**
- `prefix_index`, `text_index`, `page_summary`, `filter_in`, `query_planner` have ZERO external callers — completely isolated
- `db_query.spl` uses linear scans over `[DbRow]`, ignoring all Phase 2/3 helpers
- `db_persistence.spl` DbTable has no update method and no index awareness
- `app/optimize` only handles MIR compiler passes (O0-O3 levels)
- Two executor surfaces exist: simple DbTable and pure_sql/database.spl — this task targets DbTable

**Files to modify:**
- `src/lib/nogc_sync_mut/db/db_persistence.spl` — add index fields, update method, invalidation hooks
- `src/lib/nogc_sync_mut/db/db_query.spl` — use indexes + planner instead of linear scans
- `src/lib/nogc_sync_mut/db/__init__.spl` — export new symbols
- `src/app/optimize/main.spl` — add --db-analyze flag
- `src/app/optimize/analyze.spl` — add DB query pattern analysis
- New test spec for the integrated behavior

### 2-research
<pending>

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
