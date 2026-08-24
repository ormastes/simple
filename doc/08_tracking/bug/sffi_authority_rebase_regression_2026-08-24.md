# SFFI authority census regression after mainline rebase

**Status:** Open  
**Observed:** 2026-08-24  
**Scope:** owned Simple sources and tests scanned by
`sffi-call-authority-census.shs`

## Evidence

Before rebasing the cache-GC branch, the census reported 21,382 raw calls,
2,079 explicit-authority calls, and 19,303 missing-authority calls. Rebasing
onto `origin/main` added 55 missing-authority calls outside the cache-admission
slice. Cache admission then moved eight calls to lexical `unsafe(ffi)`, yielding
21,436 raw, 2,086 explicit, and 19,350 missing: a net regression of 47.

## Required resolution

Generate the full call-site table on current main, assign each added call to its
canonical owner, and either migrate it to a checked typed wrapper or add the
smallest lexical `unsafe(ffi)` scope with a documented sentinel/ownership
contract. Do not merely lower the baseline. Preserve provider-call cardinality,
allocation behavior, and hot-path complexity. No row may be called verified or
signed without exact artifact evidence admission.
