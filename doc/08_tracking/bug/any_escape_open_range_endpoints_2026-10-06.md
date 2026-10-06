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

The HIR Range declaration still describes its start/end as required expressions,
although lowering, resolution, inference and MIR range-loop lowering treat them
as optional. Other visitors/substitution passes also assume required bounds.
Correcting this declaration requires schema regeneration and verification of
all consumers. This mismatch remains tracked; this traversal repair does not
claim to resolve every consumer or qualify the native compiler.
