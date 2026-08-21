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

The first attempted fix constructed aligned `callable_names` and
`callable_values` arrays. A fresh Stage 3 then segfaulted during Phase-2 surface
parsing after 11 releases: duplicating the same nested value aggregate in a
dictionary and array was not a safe promotion graph.

`ModuleSurfaceCallable` is now a reference-semantic class. The dictionary
therefore transports one promoted owner pointer instead of returning or
duplicating the large nested struct value; names and membership remain
unchanged. No callable is retained in a second aggregate array. A bootstrap
source contract requires the class owner and forbids the rejected value array.

## Resume

Run one fresh Stage-2 admission, produce its planner-admission-v2 receipt, then
run one receipt-bound deploy. The first Stage-3 HIR module must contain zero
`[hir-fatal]` records, and full Stage 4 plus bootstrap must-check must pass
before the push ledger can be promoted.
