# Interpreter/compiler: .get(i) on module-level array vars fails with "unknown extern function: rt_args_count"

**Date:** 2026-07-04
**Severity:** medium (silent-ish — semantic error at eval time, misleading message)
**Status:** source-fixed; focused interpreter execution pending

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

## Resolution (2026-07-16)

Static tracing found that module and local receivers already share method
dispatch. The stale `rt_args_count` diagnostic hid the current root: native
array `.get(i)` was absent from both live pure-Simple interpreter dispatchers.
Both now validate arity and integer indices, bounds-check, and return the raw
element. The interpreter regression spec covers local and module-level arrays;
execution awaits a permitted pure-Simple test binary.
