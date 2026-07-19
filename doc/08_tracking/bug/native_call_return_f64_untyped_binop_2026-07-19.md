# User-fn f64 return is untyped in JIT binop coercion → garbage compare

- **id:** native_call_return_f64_untyped_binop_2026-07-19
- **status:** open
- **severity:** medium (silent wrong result for `f(...) <cmp> <f64>` when `f` is a user fn returning f64)
- **backend:** seed cranelift-JIT / `run` path (build_vreg_types). Orthogonal to the f64 heap-box precision fix.

## Symptom

Comparing a user function's f64 return value directly against a float literal
gives the wrong answer, even for values with no precision issue:

```simple
fn first(xs: [f64]) -> f64:
    return xs[0]

fn main() -> i64:
    val a = [0.1, 0.2, 0.3]
    if first(a) == 0.1:   # <-- stays false
        return 30
    return 40
```

Returns 40. But the value is actually correct — proven two ways:
- `print(first(a))` prints exactly `0.1`.
- The store-to-local form is right: `val x = first(a)` then `if x == 0.1` → 30.

So only the *inline call-result comparison* path is broken.

## Root cause

`build_vreg_types` (`src/compiler_rust/compiler/src/codegen/instr/body.rs:220`)
only assigns a result type to `Call` instructions whose target is in a hardcoded
list of runtime functions. A call to a **user** function returning `f64` is left
untyped, so downstream binop coercion treats the (boxed / raw-bits) result as an
integer and emits `fcvt_from_sint` (signed-int→float numeric convert) instead of
a bitcast/identity — turning the f64 bit pattern into a garbage float. The `==`
against the real `0.1` then fails.

## Fix direction

Propagate user-function call return types into `build_vreg_types` (whole-program
call-return-type propagation from the HIR/MIR function signatures), so a `Call`
to a user fn returning F64 stamps its dest VReg as F64 and the binop path
coerces correctly (bitcast, not `fcvt_from_sint`). Needs a seed rebuild to
verify.

## Regression guard

Once fixed, add `if first(a) == 0.1` (the inline call-result-compare form) as an
expected-30 case. Until then the f64 precision spec deliberately uses the
store-to-local form
(`test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl`).
