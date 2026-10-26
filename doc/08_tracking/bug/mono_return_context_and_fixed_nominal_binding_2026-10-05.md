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

## 2026-10-25 argument-evidence candidate (OPEN)

The existing checked-result-context repair did not infer the argument types of
bare builtin Ok/Err calls or unresolved local inherent method calls. A guarded
direct-pass baseline established four unresolved partial-Result calls and three
unresolved impl-Result calls, with zero queued symbols/bodies. Every diagnostic
reported missing concrete local argument evidence. The rejection is deliberate
and remains unchanged; expected return context cannot authorize unknown input.

The candidate assigns explicit serialized compiler-owned Result constructor tags
only after lexical lookup misses. Mono derives a partial Result from one concrete
payload of such a tagged call, and validates the whole partial shape and payload
owner. User functions with the same printed name do not receive constructor
identity. A second, local-only path recovers a concrete declared method result
only from exact qualified lookup plus positive nongeneric inherent-impl ownership.
Trait/unsupported associations poison that proof even if the same symbol also
appears in an inherent impl. Imported and dynamic methods remain unanswered.

Final bounded cycle: eight executed, six passed, two failed, zero skipped/dropped;
peak RSS921,248KiB, raw status1, quiescent1, all recorded inputs unchanged. Six
passing cases establish unknown-argument rejection, user-Ok shadow rejection,
payload/context conflict rejection, exact local inherent method return evidence,
trait-only rejection, and trait/inherent symbol collision rejection in both orders.
The two original direct-pass examples encountered an rt_enum_id enum typed-ABI
error before completed specialization/body evidence. Do not call those examples
fixed or dismiss their failures as preexisting without an equivalent baseline.
The same ABI error class was observed in separate earlier cases; that fact does
not prove causation for these two changed paths. Six-cycle cap reached; no retries.

Retained receipts in the review worktree:
- generic-context-qualification-20261025-02:12executed8passed4failed.
- generic-nominal-qualification-20261025-01:8executed8passed.
- generic-context-direct-owner-diagnostic-20261025-01 and -02:2executed0passed.
- generic-context-result-evidence-postfix-20261025-01:8executed6passed2failed.

@workaround: the retained/local method-ownership proof is not serialized in the
archive-facts transport; archive-restored workers without it fail closed. The
portable-body validator's refusal of nonzero builtin tags remains intact, so the
new Result tags are not a claim of portable/archive qualification. These are
explicit compatibility limits pending separate native Phase3 evidence, not a
reason to relax the validator. Both original source workarounds remain in place.
No runtime, SFFI, fixed Phase2, Rust, or frozen-source changes were performed.
