# BUG: native path — first-class lambda values unsupported (CallIndirect through non-inlined lambda)

**Status:** SOURCE FIX IMPLEMENTED; STRICT EXECUTION PENDING

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

## Resolution (2026-07-15)

MIR lowering now lifts stored and passed lambdas, materializes captured values
in a runtime closure environment, and keeps the existing raw-function-pointer
call path. Both the C runtime and pure-Simple `simple-core` runtime reject
non-member tagged values before dereferencing them; the C registry is
synchronized and allocation/publication failures return nil.

`scripts/check/check-native-capturing-lambda-values.shs` covers hosted and
simple-core runtimes with default LLVM and explicit Cranelift, strict no-stub
fallback, scalar and struct captures, a raw named function, and a tagged-looking
non-member. Execution awaits a fresh runnable pure-Simple compiler artifact.

## Related

- bdd `it`-block typed block-lambdas return nil in the interpreter test
  runner (same first-class-lambda family, interpreter side).
