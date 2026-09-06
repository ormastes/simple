# HIR comprehension-clause children are omitted

**Status:** Fixed in current compiler-performance branch; execution unverified
**Area:** generated HIR traversal / typed performance facts  
**Observed:** 2026-08-24

## Evidence

`visitor_gen.spl` unconditionally skips a struct field named `kind` in its
generic wrapper traversal. That is correct for the four base carriers, whose
kind enums are matched separately, but not for wrapper structs such as
`HirCompClause`. As a result, both `hir_children_of_comp_clause` and
`hir_expand_comp_clause_child_frames_reverse` are empty even though
`HirCompClauseKind.For` and `.If` contain expressions.

## Impact

Typed `PerfFacts` does not visit iterable/filter expressions owned by
comprehension clauses. Collection operations there can be missed, making
coverage appear stronger than the traversed graph warrants.

## Resolution

The generator now skips `kind` only for base carriers. Non-base wrapper structs
classify the field normally, repairing `DimExprKind`, `EffectKind`, and
`HirCompClauseKind` across recursive visit, child enumeration, structural hash,
and frame expansion. A focused typed-PerfFacts fixture pins `For` iterable and
`If` condition discovery and order. Comprehension analysis remains explicitly
incomplete because cardinality/execution-domain modeling is still pending; the
repair does not authorize transforms.
