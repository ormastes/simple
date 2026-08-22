# Query lint remaining nested-scan hotspots

## Status

Open. Source locations, GC import projection, `UNUSED001`, and `RET001` no longer
multiply warning/candidate count by source suffix length. Other compatibility checks
still contain bounded nested work.

## Remaining candidates

- Closure-capture analysis walks backward for every nested function and compares every
  captured outer variable with every closure body line.
- Match analysis uses linear arrays for duplicate-arm checks, variant membership, and
  enum inference, which can become quadratic on generated high-cardinality matches.
- Unreachable-after-return recovery scans forward, although it normally stops at the
  next sibling statement; a shared indentation index could own this query too.

## Completion condition

Each rule consumes shared indexed source or typed-HIR facts; generated cardinality
fixtures bound work and allocations; exact diagnostic order, code, severity, and source
span are preserved or a deliberate semantic correction is documented. Unknown typed
facts fail closed rather than upgrading textual heuristics.
