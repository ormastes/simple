# Stage-3 ModuleSurface callable dictionary payload corruption (2026-08-21)

## Status

Callable ownership fix verified through all 664 Stage-3 surface parses. The
remaining cross-stage import-route aggregate reads are replaced by frozen
scalar projections; final bootstrap verification is pending.

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

The first attempted fix constructed aligned `callable_names` and
`callable_values` arrays. A fresh Stage 3 then segfaulted during Phase-2 surface
parsing after 11 releases: duplicating the same nested value aggregate in a
dictionary and array was not a safe promotion graph.

`ModuleSurfaceCallable` is now a reference-semantic class. The dictionary
therefore transports one promoted owner pointer instead of returning or
duplicating the large nested struct value; names and membership remain
unchanged. No callable is retained in a second aggregate array. A bootstrap
source contract requires the class owner and forbids the rejected value array.

The next receipt-bound run proved that fix: Phase 2 parsed and released all 664
entry-closure surfaces without a segmentation fault. HIR then reported 1,352
fatal diagnostics involving seven unresolved imported types. Both remaining
route consumers still read nested `ParserImport`/`ImportItem` value aggregates
from a staged `ModuleSurface`, even though target identity was already frozen
into scalar arrays.

`ModuleSurface` now freezes each import's item offset/count plus flattened
source and local names. Alignment validation proves monotonic, in-bounds,
exhaustive coverage. Explicit callable dependency materialization and recursive
re-export traversal consume only those scalar projections; empty counts retain
the existing glob/module-route meaning.

## Resume

Run the third and final fresh Stage-2 admission and one receipt-bound deploy.
Stage 3 must finish with zero `[hir-fatal]` records; full Stage 4 and bootstrap
must-check must pass before the push ledger can be promoted.
