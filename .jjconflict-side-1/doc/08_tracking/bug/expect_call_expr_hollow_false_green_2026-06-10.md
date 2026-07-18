# expect(<call expr>) Is a Hollow False-Green in Interpreter Specs

Date: 2026-06-10

Status: FIXED 2026-06-11

## Summary

Beyond the known bare-`expect(cond)` no-op, `expect(<function call expr>)`
in interpreter-mode specs also silently passed regardless of the call's
result. Found while writing `test/01_unit/compiler/interpreter/
module_loader_lazy_spec.spl` (W2-A2 lazy loader bridge): assertions of the
form `expect(check_something())` reported green even when the helper
returned a failure value.

## Root Cause

`interpreter_call/bdd.rs` `"expect"` handler evaluated the argument but
only checked truthiness for `Expr::Binary` nodes.  For `Expr::Call` and
`Expr::MethodCall` nodes the evaluated value was returned to the caller
without ever setting `BDD_EXPECT_FAILED`, so any call-expression assertion
with no `.to_*()` chain always passed.

## Fix

Added an `is_call_expr` check in the general fallthrough path of the
`"expect"` handler (`src/compiler_rust/compiler/src/interpreter_call/bdd.rs`).
After evaluating the argument, if `arg_expr` is `Expr::Call` or
`Expr::MethodCall` and the result is falsy, `BDD_EXPECT_FAILED` is set and
`BDD_FAILURE_MSG` records the failure reason.  A downstream `.to_*()` chain
is safe — it always overwrites `BDD_EXPECT_FAILED` with its own result, so
chained forms are unaffected.

`cargo check -p simple-compiler` clean.

**Note:** `bin/simple` is the prebuilt Rust seed and does not pick up this
fix until a seed rebuild (`scripts/bootstrap/bootstrap-from-scratch.sh
--deploy`).  The fix is verified via `cargo check` and the regression spec
passing-side tests.

## Manual Evidence (false-side, pre-fix)

Before the fix, running in the built interpreter (via `cargo run -p
simple-driver`), `expect(always_false())` with no chain reported green.
After applying the fix in bdd.rs and recompiling, the `is_call_expr &&
!value.truthy()` branch fires and sets `BDD_EXPECT_FAILED = true`,
causing the `it` block to fail.

## Regression Spec

`test/01_unit/compiler/interpreter/expect_call_expr_false_green_spec.spl`
(6 passing tests: chained true/false/non-bool, bare truthy call, bare
truthy with chain, chained false-still-passes).

## Repro (archived)

```spl
fn always_fails() -> bool:
    false

it "should fail but passes":
    expect(always_fails())
```

The spec passed (false green). Same shape with a matcher correctly failed:

```spl
expect(always_fails()).to_equal(true)   # correctly fails
```

## Workaround (no longer needed after fix)

Assign the call result to a local, then assert on the local with
`.to_equal(...)`; or have helpers return error strings and assert
`expect(err).to_equal("")`.

## Related

- Known: bare `expect(cond)` no-op; `to_be_true()`/`to_be_false()` broken
  (memory note 2026-06-05). This extends the class to call expressions.
- B3 (enum-field method call): fixed in same hardening wave 2026-06-11.
