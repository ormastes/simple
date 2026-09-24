## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: RESOLVED 2026-05-27 -- by design; use `me method(...)`

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Bug: Parser rejects `mut fn` method syntax

Status: RESOLVED 2026-05-27 -- by design; use `me method(...)`

**Date:** 2026-05-27
**Status:** RESOLVED 2026-05-27 -- by design; use `me method(...)`
**Severity:** Low
**Component:** Parser

## Symptom

```
error: compile failed: parse: Unexpected token: expected identifier, found LParen
```

Attempting to declare `mut fn method_name()` to indicate a mutating method fails at parse time.

## Context

The interpreter rejects `self.field = value` in regular methods. A `mut fn` keyword would allow explicit opt-in to field mutation. However, the parser does not recognize this syntax.

## Note

This may be by design — Simple may not intend to have `mut fn` syntax. If so, the `self.field = value` rejection in the interpreter (see `interpreter_self_field_assign_rejected_2026-05-27.md`) is the real bug to fix.

## Resolution

Simple's supported mutable-method declaration syntax is `me method_name(...)`,
not `mut fn method_name(...)`. This is documented in:

- `doc/07_guide/language/syntax.md`
- `doc/07_guide/getting_started.md`

The parser also has targeted diagnostics for Rust-style mutable-method mistakes
(`RustFnMut`) that point users to `me`.

The related interpreter bug that rejected `self.field = value` in regular
methods was fixed separately in
`doc/08_tracking/bug/interpreter_self_field_assign_rejected_2026-05-27.md`, so
there is no remaining need to add a second `mut fn` spelling.
