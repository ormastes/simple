# Interpreter/compiler: .get(i) on module-level array vars fails with "unknown extern function: rt_args_count"

**Date:** 2026-07-04
**Severity:** medium (silent-ish — semantic error at eval time, misleading message)
**Status:** RESOLVED (2026-08-09, not reproducible — see Re-verification below)

## Symptom

`.get(i)` method calls on MODULE-LEVEL array `var`s fail at evaluation:

```
semantic: unknown extern function: rt_args_count
```

while `.get(i)` on LOCAL arrays works pervasively (e.g. `tokens.get(pos)`
throughout formula.spl).

## Repro context

Found implementing LET's binding stack: module-level
`var _let_names: [text]` / `_let_values: [text]` in
src/app/office/sheets/formula.spl; `_let_names.get(i)` triggered the error.
Isolated via a bisection ladder (stub return → hardcoded index → real call)
to pin the exact broken call form.

## Workaround (in use)

Bracket indexing on module-level arrays: `_let_names[i]` — matches the
established `_di_names[idx]` precedent in di_runtime.spl.

## Next step

The method-dispatch path for module-level var receivers appears to resolve
builtin array methods differently from locals (falls through to an extern
lookup). Likely near the interpreter's method-call resolution for global/
module bindings. Cross-ref the module-var findings ledger:
[[interp_cross_module_struct_field_collision_2026-07-04]] (different bug,
same "module-scope resolution differs from local" family).

## Re-verification 2026-08-09 — NOT REPRODUCIBLE, marking RESOLVED

Reproduced the exact repro shape (module-level `var _names: [text]`, `.get(i)`
called from a function) on the currently deployed seed binary
(`bin/release/x86_64-unknown-linux-gnu/simple`, seed-warning banner
confirmed) under both default `bin/simple run` and
`SIMPLE_EXECUTION_MODE=interpret`: `.get(0)/.get(1)/.get(2)` all resolve and
return the correct elements, with no `unknown extern function: rt_args_count`
error. No source change was needed. Regression gate landed:
`test/01_unit/language/module_var_array_get_method_spec.spl` (`3 examples, 0
failures`).

**Status: RESOLVED** (verified fixed upstream, no code change required).
