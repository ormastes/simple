# for-in #143 on Optional-array variant payload binder

Symptom: `case StringLit(_, interps): if interps != nil: for it in interps` -> "for-in over non-array iterables (#143)", collection mir type I64 (generated/hir_visitor.spl:188).

Root cause: the match binder keeps its declared HIR type `[HirInterpolation]?` (Optional(Array)) via remember_local_hir_type (switch_operators_calls.spl), but `lower_for_iterator` (50.mir/mir_lowering_stmts.spl) only handled Optional(Any), so the word-typed binder fell through to #143.

Fix: lower_for_iterator peels Optional(Array|Slice) from the declared HIR type, takes the element type from the inner array, and unwraps a Tuple-typed option via option_payload_or_self before the indexed loop. Plain arrays unchanged.

Spec: test/01_unit/compiler/50.mir/for_in_optional_array_payload_binder_spec.spl (NOT executed). Fix unverified by bootstrap. Workaround `(xs ?? [])` can be removed after a Stage 2 redeploy.
