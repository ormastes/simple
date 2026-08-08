# Interpreter/compiler: .get(i) on module-level array vars fails with "unknown extern function: rt_args_count"

**Date:** 2026-07-04
**Severity:** medium (silent-ish — semantic error at eval time, misleading message)
**Status:** open — workaround in use

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
