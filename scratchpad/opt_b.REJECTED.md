# opt_b.patch — REJECTED (do NOT land as-is) — 2026-07-13

#169 Part B (native bare Some/None + .?/??). 255 lines, 3 files
(expressions.spl, module_lowering.spl, expr_dispatch.spl). Verified by me on
origin tip 4a890c80331; rejected on TWO defects (advisor-confirmed):

1. SSA-name collision (loud symptom): a program mixing `.?` + `??` + `match`
   (or `??` on `i64?`) fails llc with "multiple definition of local value named
   'l36'/'l68'" (#131/#171-class: the new `.?`/`??` alloca temps aren't
   uniquified). Single isolated `Some(9) ?? 42` builds; TWO plain `??` build;
   but realistic mixed usage (b.spl: match+2×.?+2×??) does NOT. Worker's
   isolated single-construct tests + the 15-case matrix all missed it.

2. disc==1 predicate (the REAL disqualifier): the fix makes the GLOBAL `.?`/`??`
   presence predicate `rt_is_some(x) AND rt_enum_discriminant(x) != 1`. Because
   lower_enum_construct_named hardcodes enum_id=0, the runtime stores no enum
   identity, so ANY enum handle with disc==1 (Result Err, a user enum's 2nd
   variant) reads as ABSENT under .?/??, not just Option None. Cannot be
   certified native==oracle on non-Option operands. A CORRECT predicate needs a
   real enum_id in the presence check — which lives in the FENCED
   switch_operators_calls.spl (lower_enum_match owns discriminant dispatch). So
   correct Some/None is a LARGER CROSS-LANE change, not a bankable near-miss.

DO NOT "fix the SSA collision and land": that converts today's loud build-fail
into an UNVERIFIED .?/?? result = the loud->silent conversion we reject.

Separable value: the `??` phi->alloca re-lowering fixes a genuine pre-existing
llc "PHI nodes not grouped at top" verifier bug (var_reassign_ssa spills phi
inputs to allocas) INDEPENDENT of Option semantics. If ??-codegen matters on its
own, redo it as an ISOLATED task (own switch_operators_calls + core_codegen,
uniquify temps) — do NOT extract it from this entangled patch under pressure.
