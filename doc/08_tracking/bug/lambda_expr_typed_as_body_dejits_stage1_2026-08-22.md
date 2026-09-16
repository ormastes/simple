# Seed: lambda expression typed as its BODY type de-JITs the whole stage1 closure — 2026-08-22

## Status
FIXED 2026-08-22 (seed, HIR lowering). Commit: see below.

## Symptom
JIT coverage census of the stage1 closure (deployed seed, hello-world input so
only module loading + JIT decision run):

```
SIMPLE_JIT_COVERAGE=1 simple run src/app/cli/bootstrap_main.spl compile hello.spl
[jit-coverage] de-jit whole-module reason=jit-compile-error path=src/app/cli/bootstrap_main.spl
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
  Module error: function 'check_shb_freshness' creates a lambda/closure the JIT
  closure ABI cannot compile (the closure handle is scalar-boxed (an `any`-typed
  slot), which shifts the pointer and corrupts it); JIT would return wrong values
  or crash; deferring to interpreter
```

The `run`/JIT lane is whole-PROGRAM: `load_module_with_imports` flattens the
entire closure into one module and one refusal interprets all of it. So the
whole self-hosted compiler (all 600+ modules of stage1) ran in the tree-walk
interpreter because of ONE lambda:

```
# src/compiler/80.driver/watcher/watcher_client.spl:54
validate_shb(source_path, shb_path, fn(p: text) -> i64: 0)
# src/compiler/80.driver/cache/cache_validator.spl:93
fn validate_shb(..., get_interface_hash: any) -> CacheCheckResult
```

This is NOT the duplicate-type-name class (`Cannot infer field type`): the
census found zero HIR-lowering refusals on this closure; the first and only
refusal is the closure ABI guard above.

## Mechanism
`hir/lower/expr/control.rs::lower_lambda` returned the lambda `HirExpr` with
`ty: body_ty` — the type of the lambda's BODY (`i64` here), not a function
type. Downstream:
- `mir/lower/lowering_expr_call.rs::box_arg_for_any_param` sees an `i64`
  argument flowing into an `any` parameter and emits `MirInst::BoxInt` on the
  `ClosureCreate` register. `rt_closure_new` returns a tagged heap
  `RuntimeValue`; shifting it left by 3 destroys the pointer.
- `codegen/jit.rs::first_unsupported_lambda` (correctly) refuses any module
  where a closure register reaches `BoxInt`/`BoxFloat`, so the whole program
  de-JITs instead of crashing.
- The same mis-typing made `val f = fn(x) ...; f(1)` an untyped
  `IndirectCall` (`function_signature_for_callee` found no `HirType::Function`
  on the callee), and `fn mk() -> any: return \x: ...` box the handle in the
  return slot — the two other refusal arms of the guard.
`lower_array` already worked around this for lambda ELEMENTS by building a
`HirType::Function { params, ret: body.ty }`, and `function_signature_for_callee`
already reads that type back, so the function type is the representation the
rest of the pipeline expects.

## Fix
`lower_lambda` registers `HirType::Function { params, ret: body_ty }` and uses
it as the lambda expression's type. No MIR/codegen/runtime change; the closure
ABI and value representation are untouched — the handle simply stops being
boxed as a scalar because it is no longer typed as one.

## Measurement
FILLME

## Pins
- `src/compiler_rust/compiler/src/mir/lower/tests/closure_call_types.rs`
  `lambda_passed_to_any_param_is_not_scalar_boxed` (fails pre-fix: `BoxInt` on
  the closure register in `main`) and
  `lambda_value_has_function_type_not_body_type`.
