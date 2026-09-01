# Query lint remaining nested-scan hotspots

## Status

Open. Source locations, GC import projection, `UNUSED001`, and `RET001` no longer
multiply warning/candidate count by source suffix length. Other compatibility checks
still contain bounded nested work.

## Remaining candidates

- Closure-capture analysis now resolves the nearest prior lower-indent boundary with a
  prefix-maximum Fenwick index and advances declaration counts once per exact
  `(boundary, closure-indent)` group. Sibling closures no longer rebuild the same map or
  walk the outer body backward. Nested closure bodies can still be scanned by each
  containing closure because that duplication is observable in legacy diagnostic output;
  a future exact replacement should index assignment intervals and emit stored results in
  closure/body order.
- Match analysis now indexes duplicate arms and per-enum variant membership. It still
  tests each pattern against each candidate enum during ambiguous type inference; typed
  scrutinee facts should eventually remove that heuristic candidate search.
- RET001 and both UNREACH001 query projections now share caller-owned reverse indentation
  facts in their main paths. Compatibility wrappers may construct the same linear index
  when invoked independently.

## Completion condition

Each rule consumes shared indexed source or typed-HIR facts; generated cardinality
fixtures bound work and allocations; exact diagnostic order, code, severity, and source
span are preserved or a deliberate semantic correction is documented. Unknown typed
facts fail closed rather than upgrading textual heuristics.
