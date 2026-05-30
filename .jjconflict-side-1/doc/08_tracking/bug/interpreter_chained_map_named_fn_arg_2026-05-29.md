# Interpreter: named function passed to non-chained array map fails

Date: 2026-05-29
Status: FIXED 2026-05-29

## Symptom

In interpreter mode, calling `.map(fn_name)` with a named function on a
non-chained array fails with "expected lambda argument":

```simple
fn get_idx(e) -> i64:
    e.0
val result = [(0, "x"), (1, "y")].map(get_idx)
# Fails: semantic: expected lambda argument
```

The same pattern works when the array is the result of a chained call:

```simple
fn get_idx(e) -> i64:
    e.0
val result = ["x", "y"].enumerate().map(get_idx)
# Passes: result = [0, 1]
```

## Impact

Named function arguments to `.map()`, `.filter()`, `.any()`, `.all()`
etc. do not work on direct/literal array receivers in interpreter mode.
Lambda arguments (`\e: e.0`) work correctly after the fix for
`spipe_interpreter_tuple_map_result_matcher_binding_2026-05-27`.

## Root Cause

`apply_lambda_to_vec` in
`src/compiler_rust/compiler/src/interpreter_helpers/collections.rs`
only handles `Value::Lambda`. When a named function is passed (producing
`Value::Function { def, captured_env, .. }`), it falls through to the
error path:

```rust
} else {
    Err(CompileError::semantic_with_context("expected lambda argument", ...))
}
```

The chained call path goes through `call_method_on_value` in
`method_dispatch.rs` which checks `Value::Function` first (and was fixed
in the 2026-05-27 bug to also handle `Value::Lambda`). The non-chained
path through `handle_array_methods` uses `eval_array_map` → `apply_lambda_to_vec`
which lacks the `Value::Function` arm.

## Fix

Add a `Value::Function` arm to `apply_lambda_to_vec` (and the matching
helpers for filter/any/all) using `exec_function_with_values`, mirroring
what `call_method_on_value` already does. This is the symmetric complement
of the 2026-05-27 fix.

## Repro

```bash
src/compiler_rust/target/debug/simple run /tmp/named_fn_map_spec.spl --mode=interpreter
```

Spec:
```simple
fn get_idx(e) -> i64:
    e.0
val result = [(0, "x"), (1, "y")].map(get_idx)
expect(result).to_equal([0, 1])
```

Expected: passes.
Actual: fails with "semantic: expected lambda argument".
