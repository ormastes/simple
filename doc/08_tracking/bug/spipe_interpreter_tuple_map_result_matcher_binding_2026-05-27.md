# SPipe interpreter tuple-map result matcher/binding regression

Status: Fixed 2026-05-29. All repro cases pass in interpreter mode.

Date: 2026-05-27

## Symptom

In SPipe interpreter mode, an expression using `enumerate().map(...)` over tuple
fields evaluates correctly when used directly in a boolean equality assertion:

```simple
expect(["i64", "bool"].enumerate().map("{_1.0}:{_1.1}") == ["0:i64", "1:bool"]).to_equal(true)
```

The same value fails the spec when first bound to a local `val` and asserted
through `to_equal`, and the failure also reproduces with an explicit lambda:

```simple
val result = ["i64", "bool"].enumerate().map(\e: e.0)
expect(result).to_equal([0, 1])
```

Native mode passes the isolated case, and `simple check` accepts it.

## Impact

This is not a placeholder parser failure: `_1.0` and `_1.1` inside interpolated
placeholder callbacks parse and evaluate correctly in interpreter expressions.
The defect appears specific to SPipe interpreter execution around bound
tuple-map results and/or `to_equal` matcher comparison/reporting.

## Repro

Create a temporary spec with the explicit-lambda example above and run:

```bash
src/compiler_rust/target/debug/simple test <spec> --mode=interpreter --clean --format json
```

Expected: 1 passed.
Actual: 1 failed with no per-assertion error in JSON output.

## Root Cause

`call_method_on_value` in
`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`
is the dispatch path used by `handle_method_call_with_self_update` when
processing **chained** method calls (receiver is a temporary expression,
not a stored identifier).

This function's `"map"`, `"filter"`, and `"flat_map"` handlers only
matched `Value::Function` (named functions). When the argument was a
`Value::Lambda` (the result of evaluating an inline lambda `\e: e.0`),
the `if let Some(Value::Function { .. }) = _args.first()` branch did not
match and the function fell through to:

```rust
return Ok(Value::array(arr.to_vec()));  // returned original array unchanged
```

This caused any chained `.map(\e: ...)` or `.filter(\e: ...)` call on
the result of another method call (such as `.enumerate()`) to silently
return the original array rather than applying the lambda.

The intermediate-variable workaround (`val pairs = arr.enumerate();
pairs.map(...)`) bypassed this path because a simple variable receiver
is dispatched through `evaluate_method_call_with_self_update` via the
`Expr::Identifier` branch, which reaches the full `handle_array_methods`
dispatcher that correctly handles `Value::Lambda`.

## Fix

Added `Value::Lambda` arms to the `"map"`, `"filter"`, and `"flat_map"`
match blocks in `call_method_on_value` (same file). Each arm evaluates
the lambda body via `evaluate_expr` for every array element, matching
the existing lambda execution pattern used by `apply_lambda_to_vec`.

File changed:
`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`

The same `Value::Lambda` arm was also added to `"any"` and `"all"` in
the same function, which had the identical omission (they silently returned
wrong booleans when chained with a lambda — `any` returned `!arr.is_empty()`,
`all` returned `true`).

## Related

`doc/08_tracking/bug/interpreter_chained_map_named_fn_arg_2026-05-29.md`
covers the symmetric gap on the non-chained path: named functions passed
to `.map()` on literal arrays also fail (separate code path, separate fix).

## Status

Fixed 2026-05-29. All repro cases pass in interpreter mode.
Bug doc command (`simple test <spec> --mode=interpreter --clean --format json`)
reports `"success": true, "total_passed": 6, "total_failed": 0`.
