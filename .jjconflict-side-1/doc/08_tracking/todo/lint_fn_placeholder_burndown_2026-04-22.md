# lint_fn_placeholder_burndown

Date: 2026-04-22
Parent TODO row: 194
Status: partial fix; parent remains open

## Research

The next smallest placeholder target under the anti-dummy backlog was `test/unit/compiler/lint/test_lint_fn_spec.spl`. It already called `classify_trivial(0)`, but the second example ended with `expect(true).to_equal(true)` and a diagnostic print instead of asserting behavior.

Existing `stub_impl_spec.spl` tests show the correct way to classify an integer literal: reset the AST, create an `expr_int_lit`, pass that expression id to `classify_trivial`, and assert the returned classification string.

## Plan

Replace the tautological assertion with a concrete AST-backed `classify_trivial` assertion and remove the diagnostic print.

## Fix

Updated `test/unit/compiler/lint/test_lint_fn_spec.spl` to import `ast_reset` and `expr_int_lit`, build an integer literal, and assert `classify_trivial` returns `integer (0)`.

## Verification

- `bin/simple lint test/unit/compiler/lint/test_lint_fn_spec.spl`
- `timeout 120s bin/simple test test/unit/compiler/lint/test_lint_fn_spec.spl`
- `rg -n 'expect\\(true\\)\\.to_equal\\(true\\)|pass_todo|pass_do_nothing|pass_dn' test/unit/compiler/lint/test_lint_fn_spec.spl`
