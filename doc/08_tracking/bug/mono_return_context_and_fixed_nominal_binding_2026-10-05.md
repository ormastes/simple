# mono_return_context_and_fixed_nominal_binding_2026-10-05

Status: OPEN. Workaround source prepared; native validation UNRUN.

P3 p3-stability30577-cranelift40 naturally terminated with exit 1 after 1142
successful HIR modules and 1142 cold receipts. Worker stderr file
artifact/tmp/native-build-stderr-17380-1.log contains exactly 35 E-MONO-032
messages: cas_batch_error_v1 34; walk_hir_expr 1. Aggregate E-MONO-033
correctly refuses MIR. This was not cancellation or a cold-receipt failure.

Confirmed first cause: infer_call_type_args only unifies argument types.
cas_batch_error_v1[T](error) returns Result[T, Error], so no argument binds T.
The source workaround supplies the caller's declared Result success type at
all 34 sites (transaction, unit, text, i64), without changing error variants,
I/O, cleanup, cache publication, or the monomorphization gate.

The visitor call receives explicit MatchSiteScan, preserving the same visitor
and state. The binder currently compares module-local Named SymbolId values
on concrete parameters, despite documenting that non-generic shapes belong
to type checking. This is a source-proven defect and a candidate cause of the
visitor failure; the receipt itself does not identify which argument failed.
Do not claim exact runtime attribution without a diagnostic/reproducer run.

Underlying repair remains required: consume concrete checked call-result
context while rejecting conflicting/unresolved bindings; avoid cross-module
local-ID equality for already checked concrete parameter shapes. Preserve
owner identity for parameterized nominal types; do not guess names or types.

Regression: test/fixtures/compiler/mono_context_repro/main.spl deliberately
retains implicit return-only generic calls for i64 and array successes. It
must compile and execute with exit 0 under the repaired producer. Add direct
HIR inference conflict/missing-context cases and an imported higher-order
visitor case before declaring the root fix validated. Native tests UNRUN.

Retirement requires the original implicit calls to compile with a new actual
producer carrying the repair, focused runtime assertions, then cached P3
with all modules and zero unresolved generic calls. Explicit arguments are
not evidence that the compiler defect is fixed. No frozen source was edited.

Underlying candidate now implements checked direct-call result contexts from
expression metadata, annotated locals, function tail values and explicit
returns. Lambda context is saved/reset/restored; an untyped lambda cannot
borrow the enclosing function result. Argument/result conflicts still reject.
Fixed Named parameters with no type arguments bind nothing and no longer
compare table-local IDs; parameterized nominal checks are unchanged.

Six HIR cases assert independent scalar/array bindings, missing/Any/conflict
rejection, fixed/parameterized nominal handling, exactly one tail rewrite,
lambda isolation, and local/return specialization deduplication. No new global
cache or HIR clone was added; the pass retains one scoped optional return type.
Nominal handling adds one O(1) empty-argument check. Result unification traverses
one declared return shape per inferred call; no repeated subtree concreteness
walk was added to the recursive binder. Actual memory/performance measurements
and all new native execution remain UNRUN, not inferred PASS. General expected
context propagation through untyped if/match/block expressions remains outside
this narrow repair; existing checked expression metadata still applies.
