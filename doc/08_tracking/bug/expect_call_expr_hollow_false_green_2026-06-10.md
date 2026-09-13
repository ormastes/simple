# expect(<call expr>) Is a Hollow False-Green in Interpreter Specs

## Closed 2026-09-13 — Fixed 2026-06-11 per the entry's own status

- **inferred** The Status line reads `FIXED 2026-06-11`; the body describes `expect(<call expr>)` no longer silently passing.
- **measured** The one path-scan miss is `interpreter_call/bdd.rs`, a Rust-seed path fragment written without its crate prefix; the seed tree is present and untouched by this triage.
- **inferred** The fix is in spec-matcher evaluation, which needs `bin/simple test` to demonstrate; that command is unusable on this Windows host (killed at its outer bound even on a 6-line spec), so no fresh execution evidence could be added.


Date: 2026-06-10

Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below

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
