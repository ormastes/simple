# User-fn f64 return is untyped in JIT binop coercion → garbage compare

- **id:** native_call_return_f64_untyped_binop_2026-07-19
- **status:** fixed (seed JIT/local Cranelift calls)
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

## Resolution

The shared Cranelift backend records raw and emitted/mangled function declaration names
with their MIR return types. `build_vreg_types` consults that table before its
runtime-call fallbacks, so a local user call returning F64 stamps its destination
as F64 and the binop path preserves the value instead of converting integer bits.
The table follows the existing incremental JIT ownership rule: local bodies
replace entries, while imports only fill missing entries.

Cross-file native-project calls are a separate scope: an imported function that
is absent from the current file's `MirModule.functions` still needs authoritative
typed call metadata from project discovery rather than another name-based guess.

## Regression guard

- Rust JIT behavior: `test_jit_f64_call_result_value` includes the original
  inline `first(values) == 0.1` reproducer.
- Seed vreg unit: `build_vreg_types_uses_direct_callee_return_type`.
- Simple spec: `array_f64_element_precision_spec.spl` covers both direct array
  access and inline user-function return comparison.
