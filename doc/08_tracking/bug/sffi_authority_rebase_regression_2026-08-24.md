# SFFI authority census regression after mainline rebase

**Status:** Open  
**Observed:** 2026-08-24  
**Scope:** owned Simple sources and tests scanned by
`sffi-call-authority-census.shs`

## Evidence

Before rebasing the cache-GC branch, the census reported 21,382 raw calls,
2,079 explicit-authority calls, and 19,303 missing-authority calls. Rebasing
onto `origin/main` added 55 missing-authority calls outside the cache-admission
slice. Cache admission moved eight calls to lexical `unsafe(ffi)`. The retained
dictionary HIR slices then moved another 24 calls without changing call
cardinality, yielding 21,436 raw, 2,110 explicit, and 19,326 missing: a net
regression of 23. A later mainline rebase added five missing calls. The MIR
return-type probe and cached method-trace owners then removed twelve missing
rows, yielding 21,435 raw, 2,116 explicit, and 19,319 missing: a net regression
of 16 from the original 19,303 pre-rebase measurement. Scoping the two HIR
phase-profiler stderr flushes then yields 2,118 explicit and 19,317 missing,
reducing the net regression to 14. Scoping the three safety-severity
subprocess-policy reads yields 2,121 explicit and 19,314 missing, reducing the
net regression to 11.

## Required resolution

Generate the full call-site table on current main, assign each added call to its
canonical owner, and either migrate it to a checked typed wrapper or add the
smallest lexical `unsafe(ffi)` scope with a documented sentinel/ownership
contract. Do not merely lower the baseline. Preserve provider-call cardinality,
allocation behavior, and hot-path complexity. No row may be called verified or
signed without exact artifact evidence admission.
