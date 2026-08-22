# Query lint remaining nested-scan hotspots

## Status

Open. Source locations, GC import projection, `UNUSED001`, and `RET001` no longer
multiply warning/candidate count by source suffix length. Other compatibility checks
still contain bounded nested work.

## Remaining candidates

- Closure-capture analysis still walks backward for every nested function. Its former
  outer-variable by body-line Cartesian comparison is fixed: each body line extracts one
  assignment target and performs an indexed membership lookup.
- Match analysis now indexes duplicate arms and per-enum variant membership. It still
  tests each pattern against each candidate enum during ambiguous type inference; typed
  scrutinee facts should eventually remove that heuristic candidate search.
- Unreachable-after-return recovery scans forward, although it normally stops at the
  next sibling statement; a shared indentation index could own this query too.

## Completion condition

Each rule consumes shared indexed source or typed-HIR facts; generated cardinality
fixtures bound work and allocations; exact diagnostic order, code, severity, and source
span are preserved or a deliberate semantic correction is documented. Unknown typed
facts fail closed rather than upgrading textual heuristics.
