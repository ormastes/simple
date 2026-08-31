# Implicit-self field assignment is still a SILENT no-op in plain `fn` methods

**Date:** 2026-08-31
**Status:** FIXED (AST interpreter) 2026-08-31 — one residual, see below
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


## Fix (2026-08-31)

The root cause in the bug title was right about the SYMPTOM but incomplete about
the MECHANISM, so both halves are recorded here.

* `exec_method_body` (`src/compiler_rust/compiler/src/interpreter_control.rs:3229`)
  pre-binds every receiver field as a frame LOCAL. `Env` now records those names
  separately (`Env::mark_field_prebind` / `Env::is_field_prebind`,
  `src/compiler_rust/compiler/src/value.rs`), and the guard at
  `src/compiler_rust/compiler/src/interpreter/node_exec.rs:702` fires on
  `is_first_assignment || env.is_field_prebind(name)`. The flag is cleared by
  `mark_local` (a genuine `val`/`var`/parameter declaration) and by
  `enter_block_local` (a loop variable), so legal shadowing is untouched —
  verified directly: a `static fn` local, a `var flag = 3` shadow, and
  `for flag in [1, 2]` all still run.
* `scripts/check/check-implicit-self-field-assignment.shs` now runs **5**
  probes instead of 2 (`me` and `fn(self)` on both engine settings, plus the
  self-less `fn` shape on the interpreter). The new `fn` probes FAIL on the
  pre-fix binary and PASS on the fixed one — that is the fail-before/pass-after
  artifact.
* Rust unit tests pinning the discriminator and its clearing rules were added
  next to the existing `Env` locality tests in `interpreter_control.rs`.

## Residual — self-less `fn` in a class body diverges between lanes

`fn m():` with NO `self` parameter is marked implicitly `static` by the PARSER
(`src/compiler_rust/parser/src/types_def/mod.rs`, "No self/me param and not a
`me` method — treat as static"). HIR lowering therefore has `ctx.has_self ==
false` and `check_implicit_self_field_assignment`
(`src/compiler_rust/compiler/src/hir/lower/memory_check.rs:382`) returns early,
so the JIT/native lane still lowers a bare `field = ...` in that shape to a
throwaway local. The AST interpreter dispatches the same method as an INSTANCE
method with fields bound, and now rejects it.

Making the two agree is a design decision, not a bug fix: it requires deciding
whether a self-less `fn` in a class body is a static method (parser's view) or
an instance method (interpreter's view), and relaxing the HIR `has_self` gate
without that decision would hard-error legitimate locals inside genuinely
`static fn` methods. Left open deliberately, and asserted as
interpreter-only in the guard rather than omitted.

Note `count += 1` (AugAssign on a bare field name) was checked and is NOT a
hole: it already fails loudly with ``variable `count` not found``.
