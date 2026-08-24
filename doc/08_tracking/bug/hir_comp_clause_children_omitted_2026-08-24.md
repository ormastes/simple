# HIR comprehension-clause children are omitted

**Status:** Open  
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

## Required fix

Skip `kind` only for base carriers. Wrapper structs must traverse a node-bearing
kind field through its generated wrapper function/frame. Add exact ordering and
coverage fixtures for `For` and `If` clauses, regenerate visitors, and confirm
legacy and frame traversal remain order-equivalent. Until then, comprehension
analysis must remain explicitly incomplete and must not authorize transforms.
