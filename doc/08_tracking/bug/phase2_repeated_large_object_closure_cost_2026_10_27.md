# Repeated Large Closure Cost During Phase2 Per-Source Object Collection

**Status:** Proposed; bug database registration pending
**Observed:** 2026-10-27, Windows Phase2 diagnostic object campaign

## Observation

At the recorded 19-minute campaign snapshot, 43 source rows had reached terminal attempts. One active `src/app/bootstrap_builder/native_diagnostic_worker.spl` attempt reported a 1,362-module HIR workload after 265 seconds and used about 3.1 GiB RSS. The attempt had not completed at the snapshot.

This records measured collection cost only. It does not establish why the workload is large, whether work was repeated, or how long the complete inventory will take.

## Investigation

Measure how per-source object emission handles shared large source closures. Determine whether frontend/HIR work is repeated across requested entries and whether a safely invalidated shared closure artifact or grouped object-emission path is practical. Preserve the frozen Phase2 source and compiler authority while gathering the evidence.

## Acceptance

- Each requested source entry produces its own requested, structurally valid AMD64 COFF object; a cached dependency object cannot stand in for the entry output.
- Cache keys and invalidation account for every source and relevant compiler/runtime/toolchain input in the closure.
- A representative large-closure comparison reports wall time, peak RSS, number of requested outputs, and cache hit/miss behavior before and after any change.
- The comparison demonstrates that outputs remain bound to their requested entries and that source changes invalidate affected cached work.

## Evidence Boundary

The object campaign is diagnostic evidence. A valid COFF output does not establish source correctness, compiler qualification, or bootstrap admission. This note is a proposed performance issue; no cause or fix has been established, and no ETA is asserted.
