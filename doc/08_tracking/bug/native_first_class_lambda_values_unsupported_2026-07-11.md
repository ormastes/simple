# BUG: native path — first-class lambda values unsupported (CallIndirect through non-inlined lambda)

**Status:** OPEN (found 2026-07-11 during #138 wall census)

## Symptom

Storing a lambda in a variable / passing it as a value and calling it later on
the normal native path fails. Since the Wall-1 guard landed
(`aggregate_intrinsics.spl` translate_call_indirect), the failure is the loud
panic "indirect call with unresolved callee — likely an unresolved import or
unsupported first-class function value" instead of a nil-LocalId crash.

## Analysis

MIR lowering only supports lambdas that `try_inline_lambda_call`
(`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`) can inline
at the direct call site. A lambda that escapes as a value never materializes a
function pointer, so the eventual CallIndirect has no callee. Needs real
closure/function-pointer materialization (emit the lambda as a named function
+ pass its address, with capture handling or a no-capture-only first cut).

## Related

- bdd `it`-block typed block-lambdas return nil in the interpreter test
  runner (same first-class-lambda family, interpreter side).
