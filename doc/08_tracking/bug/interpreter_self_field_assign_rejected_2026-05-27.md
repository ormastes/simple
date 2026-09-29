## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: **RESOLVED** — root cause identified as incorrect method keyword (`fn` instead

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Bug: Interpreter rejects `self.field = value` in methods

Status: **RESOLVED** — root cause identified as incorrect method keyword (`fn` instead

**Date:** 2026-05-27
**Severity:** Medium
**Component:** Interpreter (ref_interpreter)

## Symptom

```
error: semantic: cannot modify self.not_found_handler in immutable fn method
```

Methods that assign to `self.field` fail in interpreter mode but work in compiled mode.

## Reproduction

```simple
class Foo:
    x: i32
    fn set_x(val: i32):
        self.x = val   # <-- interpreter rejects this
```

## Root Cause Analysis

**Language design:** In Simple, `fn` methods are immutable (cannot modify self
fields) and `me` methods are mutable. This is enforced by E1052
(`LowerError::SelfMutationInImmutableMethod`) at the semantic layer in BOTH
compiled and interpreter modes. The interpreter's `IN_IMMUTABLE_FN_METHOD` flag
is a runtime enforcement that matches the same rule.

The original symptom (`cannot modify self.not_found_handler in immutable fn
method`) was correct behavior — the method was declared `fn` and should have
been `me`.

## Expected

Methods that mutate `self.field` must use `me` instead of `fn`. This applies in
both compiled and interpreter modes.

```simple
class Foo:
    x: i32
    me set_x(val: i32):   # me = mutable self; fn = immutable self
        self.x = val
```

## Workaround

Use `me` methods for any method that modifies self fields.

## Impact

No parity bug between modes. The original report was caused by using `fn` where
`me` was required.

## Status

**RESOLVED** — root cause identified as incorrect method keyword (`fn` instead
of `me`). No interpreter change needed; existing E1052 enforcement is correct.
Corrected `test/01_unit/compiler/interpreter/self_field_assign_spec.spl` to use
`me` methods. A prior session had incorrectly marked this resolved and added a
test with `fn` methods, which would also fail in compiled mode.
