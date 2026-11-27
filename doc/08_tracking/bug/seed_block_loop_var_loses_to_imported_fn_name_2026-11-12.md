# Seed interpreter: a loop variable or lambda param named like an imported fn resolves to the fn

## Status

Fixed, verification-pending 2026-11-12 (lane loopvar-builtin).

## Symptom

```
use std.common.error.{error}
with_block "x":            # any block closure, incl. every spec `it` body
    for error in ["bad"]:
        error.contains("b")
```

fails with `semantic: method contains not found on type function (function
'error' was not called)`. The same loop inside a plain `fn` works.

## Root cause

`Expr::Identifier` lookup (`interpreter/expr/literals.rs`) prefers the live
module/owner global for any name that `env.is_local` does not report. The
block executor's `for` (`interpreter_call/block_execution.rs`, both sites)
used `save_pattern_scope`, which never called `enter_block_local` (only
`exec_for` did). So inside a block the loop variable was not local, and the
imported fn `error` won. The predicate-lambda helpers
(`bind_lambda_param` for filter/find/any/all, plus reduce and dict filter in
`interpreter_helpers/collections.rs`) bound params without `mark_local`, so
they failed the same way.

## Fix

`save_pattern_scope`/`restore_pattern_scope` enter/exit the names as
block-local, which also stashes and restores the outer declared int width as
before. The lambda helpers mark their params local.

Spec: `test/01_unit/language/loop_var_shadows_builtin_name_spec.spl`. Red on
the phase-1 seed: `executed=6 passed=2 failed=4`. Green on the fixed seed:
`executed=6 passed=6`.
