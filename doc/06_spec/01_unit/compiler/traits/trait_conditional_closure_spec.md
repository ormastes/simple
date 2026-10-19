# Conditional closure manual

Eleven authored SSpec cases, all UNRUN; source-predicted RED only. Real SymbolTable.define/get_symbol_raw supplies trait/binder/nominal rows, then actual TraitSolver APIs register and solve implementations.

Cases: Named/legacy binders succeed with concrete child; missing child reports actual concrete type and later registration invalidates failure; solve_all reports failure without discarded child queue; repeated child ambiguity remains typed; cycle refuses and scratch resets; repeated binder consistency; associated failure/unconstrained success/both predicate orders; Function effects preserved; finite nested conditional closure succeeds synchronously.

No replacement solver, parser-string heuristic, runtime PASS, branch coverage percentage or HM end-to-end claim. HM adapter integration and runtime execution are root-owned and remain open.

Revision2 adds nested current/unrelated Named TypeParam rejection under blanket child implementations, a same-table concrete nominal positive, missing nominal-table authority refusal, and primitive-only solver compatibility. All UNRUN.
