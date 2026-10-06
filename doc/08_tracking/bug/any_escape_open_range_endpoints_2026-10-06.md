# Any checker dereferences absent range endpoints

Status: traversal repaired; native bootstrap verification pending.

`expression_core.spl` lowers range start/end as `HirExpr?`, preserving nil
for open bounds. `any_check_expr` formerly passed both slots unconditionally
into the expression walker. The Phase 2 LLVM test-runner build completed HIR
667/667, then crashed in `any_origin_kind`, called by the Range start traversal.

The new typed-HIR spec reproduces the absent-bound failure independently:
five original cases fail with `undefined field 'kind'` on nil. Traversing
present bounds with `if val` makes all five pass. Two cases require the
E-MC-ANY-001 diagnostic for a present Any-typed endpoint. The existing nine
Any escape cases also pass. These are Phase 1 seed/interpreter results, not
native Phase 2 qualification.

Evidence: `/tmp/simple-database-export-repair/range-endpoints-baseline.log`,
`range-endpoints-fixed.log`, and `any-escape-existing-fixed.log`.
Original native stack: `gdb.log`; register/core capture: `gdb-core.log`.

The follow-up declares both HIR Range bounds optional, repairs substitution,
criticality and post-monomorphization consumers, and regenerates schema-owned
visitors/codecs. Regular and canonical codec versions change because the wire
format gains an optional-presence bit. Generated walkers/hash functions already
guard nil at entry; they were not additional independently proven crashes.
Focused schema and codec regressions pass in Phase 1. Native compiler
qualification remains pending. The separate open-ended MIR-loop finding is
tracked in `mir_open_ended_range_zero_endpoint_2026-10-06.md`.
