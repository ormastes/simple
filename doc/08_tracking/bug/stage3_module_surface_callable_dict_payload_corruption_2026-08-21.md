# Stage-3 ModuleSurface callable dictionary payload corruption (2026-08-21)

## Status

Pure-Simple owner fix implemented; bootstrap verification deferred to the next
bounded session because the prior session exhausted its three-cycle cap.

## Evidence

Three receipt-bound Stage-3 runs completed all 954 surface parses and then
reported the same impossible HIR cluster: `driver.spl` was attributed repeated
`Span` plus `OptimizationLevel` failures although it names neither type, while
`file_ops.spl` was attributed `ProcessResult` although its surface does not
declare that signature. Canonical owner-index and prebound-composite fixes did
not change the first diagnostics.

The only imported-callable payload reads were
`imported_mod.callables[imported_name]`. Names and `contains_key` survived the
staged native boundary, but the large `ModuleSurfaceCallable` dictionary value
was read as a neighboring/stale payload. That explains both the correct symbol
name and the wrong signature dependencies.

## Fix

`ModuleSurface` now constructs aligned `callable_names` and `callable_values`
arrays in one pass before promotion. Import registration finds the scalar name
index and reads the matching array payload; it fails closed if the projections
are misaligned. The retained dictionary remains for membership and other
same-stage consumers. A bootstrap source contract prevents restoring the two
cross-stage dictionary payload reads.

## Resume

Run one fresh Stage-2 admission, produce its planner-admission-v2 receipt, then
run one receipt-bound deploy. The first Stage-3 HIR module must contain zero
`[hir-fatal]` records, and full Stage 4 plus bootstrap must-check must pass
before the push ledger can be promoted.
