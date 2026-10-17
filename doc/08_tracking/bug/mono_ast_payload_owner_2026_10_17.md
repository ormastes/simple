# AST payload extraction introduces unowned generic specializations

Date: 2026-10-17
Bug: BUG-MONO-AST-PAYLOAD-OWNER-20261017
Database reconciliation: pending; no admitted bug database tool available.
Status: reproduced, repair proposed; runtime qualification pending.
Affected source: dfcfc9017fff1457316feb13dcb0411fb6b8dd20.
Producer: 0015C3FE0DFD28C22E55CBE488636F30E5BAA869D1608CAD4847685B9C553429.

Phase 3 lowered all 1301 HIR modules successfully, then rejected six local
`_sffi_tuple_get` generic instantiations in `module_callable_types.spl` with
E-MONO-041. E-MONO-033 refused to lower six unspecialized calls into MIR;
no native object or executable was produced. Full evidence is retained in
`C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase3-0015-loopsite-fixed-20261017`.

Four instantiations request Expr, one Block and one Block?. Expr is already
explicitly imported from its real owner, parser_types_expr. The producer's
nominal declaration-owner gate remains intact; no owner IDs are fabricated.
The generic-owner failure itself remains open pending a producer-level repair.

The source also projects three single-field StmtKind.Expr payloads through
rt_tuple_get. The producer's lower_enum_lit stores a single field directly and
only boxes multiple fields as tuples; the C runtime tuple getter accepts only
an array. That projection is wrong for the established native enum ABI.

Proposed repair restores the producer's own typed StmtKind-to-Expr projection
at the same three discriminant-guarded sites, with explicit
`unsafe(capabilities: [ffi])` expressions retaining the typed Expr result.
The declaration keeps its unsafe FFI contract. Producer source
0b7d87d9e0fb9f343fef2f98ee0da26abf231d8c already uses that declaration and those
calls. The If scanner uses its existing qualified three-field case with typed
rebindings, preserving its condition/then/optional-else merge algorithm. The
local generic wrapper and raw If pre-dispatch become unnecessary and are removed.
No declaration-owner gate or validation result is weakened.

The direct typed projection remains an explicit compatibility workaround for
historical Expr/StmtKind.Expr pattern collisions. Its recovery reference is
0b7d87d9e0fb9f343fef2f98ee0da26abf231d8c; do not blindly restore whole files.
Recover to ordinary qualified patterns only after a qualified native producer
passes the payload regression. Actual workaround commit SHA will be recorded
in the external freeze receipt once reviewed and committed.

Regression source distinguishes single Expr payload,
non-Expr variant, If with nil else and If with Some(Block); execution remains UNRUN. The final
authorized full-closure attempt must pass monomorphization and produce actual native
objects. Source inspection alone is not native qualification.
