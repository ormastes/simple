# MIR: let-annotated Result type overwritten by untyped join metadata (2026-11-12)

Status: OPEN (filed, not fixed). Severity P3.

## Symptom
`val r: Result<i64, text> = if/match ... Ok(x_u8) ...`. The MIR local's HIR type metadata becomes
`Result<u8, text>` instead of the declared `Result<i64, text>`.

## Cause
At `src/compiler/50.mir/mir_lowering_stmts.spl:1799-1808`, `let_declared_type_override_v1` returns 0 for a
Result initializer, so `copy_local_hir_type_metadata` writes the untyped-join type over the annotation.

## Reachable value path
`enum_match_expr_type` (`_MirLoweringExpr/switch_operators_calls.spl:2630`, Var arm reads
`find_local_hir_type`) -> `result_ok_hir_type` (`_MirLoweringExpr/method_calls_literals.spl:544`) ->
`lower_result_unwrap_core`, which sets `result_type = self.lower_type(payload_type)` (around :1054/:1070).
So `r.unwrap()` gets MIR type U8, not I64.

## Why no wrong value has been seen yet
The witnessed values fit in 8 bits, and `mir_narrow_unsigned_integer_common_type`
(`_MirLoweringExpr/expr_dispatch.spl:200-227`) widens narrow-unsigned arithmetic to i64. A consumer that
honours U8 width directly could truncate: a u8 array store (`mir_lowering_stmts.spl:926-942`), or passing
`r.unwrap()` as a call argument.

## Origin
Found in the Fable review of PR #8499. The issue predates it; #8486 and #8499 did not widen it.

## Suggested fix
`let_declared_type_override` should prefer the declared annotation for Result initializers.

## Suggested repro
`val r: Result<i64, text> = if c: Ok(x_u8 + 0u8) else: Err("e")`, then store `r.unwrap() + 300` into an
i64 array, or pass it to `fn f(v: i64)`, and print it. Expected 300+x; a U8-honouring consumer would truncate.
