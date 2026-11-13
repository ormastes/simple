# decorator_fn_arm_drops_implicit_return_2026-11-14

- **Severity:** P3. **Status:** open.
- **Found by:** `test_private_access_closure_guard_paths_2026-11-14` (decorator fixture).

## Symptom

A named `fn` used as a runtime decorator decorates to nil when it returns its
result by implicit last expression. The decorated name then fails at its call:

```
use app.runner.deco.{apply_dec}       # applies `@dec` to a nested fn, then calls it
fn mk(f: fn() -> i64) -> fn() -> i64:
    val x = 42
    \: x                                # implicit return
print apply_dec(mk)
```

```
error[E1002]: function `inner` not found
```

`return \: x` instead of the implicit form runs and prints `42`. A lambda
decorator (`\f: ...`) is not affected.

Measured on the seed built from `549b28a2777` (before the guard-path fix) and
after it, on both the default lane and `SIMPLE_EXECUTION_MODE=interpret`:
rc 1 with `function inner not found`; with `return`, rc 0 and `42`.

## Cause (suspected)

`call_value_with_args` (`interpreter_eval.rs`) runs a `Value::Function`
decorator with `exec_block` and `control_to_value`, not through
`execute_function_body`. The implicit last-expression value of the body is
lost on that path, so the decorator returns nil and `inner` is rebound to nil.

## Not done here

The fixture in `test_private_access_matrix_spec.spl` uses an explicit `return`
so it tests the visibility rule only. Fixing the return value means routing
the arm through the normal function body path, which is a separate change.
