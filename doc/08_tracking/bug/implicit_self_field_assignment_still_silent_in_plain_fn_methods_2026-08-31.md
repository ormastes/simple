# Implicit-self field assignment is still a SILENT no-op in plain `fn` methods

**Date:** 2026-08-31
**Status:** OPEN
**Severity:** high (silent data-loss class; same class as
`interp_implicit_self_field_assignment_silent_noop_2026-07-17.md`, which is
marked FIXED)

## Symptom

The 2026-08-08 fix for implicit-self field assignment fires for `me` methods
but NOT for plain `fn` methods on a class. Reproduced on the Rust seed
(`bin/simple`, 2026-08-31):

```simple
class C:
    flag: bool = false
    me set_me():
        flag = true      # hard error, as designed
    fn set_fn():
        flag = true      # SILENT no-op — `flag` stays false, exit 0
```

`me set_me()` produces
`semantic: invalid assignment: 'flag' is a field of 'C' ...` (and the same
message from HIR lowering on the JIT path). `fn set_fn()` runs to completion
and leaves the field unchanged.

`scripts/check/check-implicit-self-field-assignment.shs` reports
`PASS — 2 engine setting(s) checked` because its fixtures use the `me` form
only, so the `fn` half of the population is unguarded.

## Root cause (AST interpreter)

`interpreter/node_exec.rs:702` guards the shape only when
`is_first_assignment` is true (`!env.contains_key(name)`). Method dispatch
pre-binds every field of the receiver as a LOCAL in the callee env — see
`interpreter_control.rs:3202` (`exec_method_body`), which does
`local_env.mark_local(k); local_env.insert(k, v)` for each field, and the
equivalent binding in `interpreter_call/core/function_exec.rs`. So `flag`
already exists as a local, `is_first_assignment` is false, the guard is
skipped, and the write lands on the doomed local.

## Where it bites

`test/feature/usage/context_managers_spec.spl` — 7 of 14 examples fail for
exactly this reason. Their `__enter__` / `__exit__` bodies are plain `fn` and
use bare `exited = true` / `cleanup_count = cleanup_count + 1`, so the field
never changes and the assertion on the outer object fails. The `with`
statement itself is NOT at fault: `__enter__` and `__exit__` are both invoked,
and with `self.exited = true` the mutation is visible to the caller
(verified directly).

## Fix directions

1. Make the `node_exec.rs:702` guard independent of `is_first_assignment` —
   e.g. consult the receiver class's declared field set rather than
   `env.contains_key`, so the pre-bound field local no longer masks it.
2. Extend `scripts/check/check-implicit-self-field-assignment.shs` with a
   plain-`fn` fixture so the gap cannot reopen.

Note that closing this makes `context_managers_spec.spl` fail LOUDLY rather
than pass: those 7 examples assert the forbidden shape mutates the field,
which contradicts the documented 2026-08-08 decision. That spec needs
rewriting to `self.field = ...`, which is a spec change and therefore out of
scope for the product-fix lane that found this.
