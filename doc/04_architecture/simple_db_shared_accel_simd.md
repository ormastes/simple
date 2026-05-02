<!-- codex-design -->
# Simple DB Shared Accel SIMD Architecture

## Scope

Phase 1 adds a shared acceleration layer at `src/lib/nogc_sync_mut/db/accel.spl`
for DB-adjacent scan workloads. The module is intentionally storage-agnostic and
is reused by:

- `src/lib/nogc_sync_mut/database/query.spl`
- `src/lib/nogc_sync_mut/db/dbfs_engine/schema.spl`
- `examples/spostgre/src/engine/scan.spl`

## Layering

1. `std.db.accel`
   - owns bitmap state, fixed-size batching, text/key predicate helpers,
     trigram extraction, and runtime capability reporting
   - depends only on `std.simd` capability detection
2. Consumer adapters
   - SDN query builder converts row arrays into batch/bitmap passes
   - DBFS schema scans use summary-hash prefilter + exact-name refinement
   - spostgre scan utilities use BRIN as a coarse filter and accel bitmaps for
     tuple-level refinement
3. Existing storage/layout code
   - remains unchanged; no constructor or pager contract changes

## SIMD Policy

- The runtime capability surface is real: `accel_capability_report()` uses
  `std.simd.detect_profile()` / `profile_name()` / `simd_width()`.
- Phase 1 kernels are behavior-identical scalar implementations.
- The shared API is the stable seam for later AVX2/NEON fast paths.
- `scalar_fallback: true` is always reported so callers can log capability state
  without branching on platform-specific details.

## Hot Paths

- SDN: filter chains now build one candidate bitmap over fixed-size batches
  instead of repeatedly allocating filtered row arrays.
- DBFS: namespace scans can summary-hash filter candidates before exact name
  comparison, preserving correctness across collisions.
- spostgre: BRIN summaries stay first-pass pruning; shared text scan helpers
  refine surviving tuples and provide a minimal token/trigram text-search path.

## Out of Scope

- learned indexes or learned cardinality estimation
- join-engine redesign
- posting-list / inverted-index execution
- ANN or vector search
