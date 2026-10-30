# for-in #143 on Optional-array variant payload binder

Symptom: `case StringLit(_, interps): if interps != nil: for it in interps` -> "for-in over non-array iterables (#143)", collection mir type I64 (generated/hir_visitor.spl:188).

Root cause: the match binder keeps its declared HIR type `[HirInterpolation]?` (Optional(Array)) via remember_local_hir_type (switch_operators_calls.spl), but `lower_for_iterator` (50.mir/mir_lowering_stmts.spl) only handled Optional(Any), so the word-typed binder fell through to #143.

Fix: lower_for_iterator peels Optional(Array|Slice) from the declared HIR type, takes the element type from the inner array, and unwraps a Tuple-typed option via option_payload_or_self before the indexed loop. Plain arrays unchanged.

Spec: test/01_unit/compiler/50.mir/for_in_optional_array_payload_binder_spec.spl (NOT executed). Fix unverified by bootstrap. Workaround `(xs ?? [])` can be removed after a Stage 2 redeploy.

## Workaround record (phase-3 adhoc lane, landed with #4302)

Status: workaround applied, root fix open. Phase-3 run-11 (8ab7cd693d8) MIR stage.

Symptom: for-in over non-array (#143), collection mir type I64 in generated/hir_visitor.spl:188: optional variant payload binder (StringLit interpolations) is I64.

Workaround (tagged `@workaround bug=for_in_optional_variant_payload_binder_i64_2026-10-24`): iterate (opt ?? []) as hir_codec.spl does.

Root fix location: src/compiler/50.mir/mir_lowering_stmts.spl (#143) and optional payload binder typing; also the generator that emits src/compiler/20.hir/generated/*.spl. Same shape exists in other generated files (hir_hash/hir_visit/hir_children use match, hir_codec uses if val).

Release/1.0.0 note: the hir_visitor.spl site is superseded by the regenerated visitor (`match b_interpolations: case Some(opt1)` form, upstream 41c06e4b940); the `?? []` workaround was not applied there.
