# Bug: Interpreter rejects `self.field = value` in methods

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
Corrected `test/unit/compiler/interpreter/self_field_assign_spec.spl` to use
`me` methods. A prior session had incorrectly marked this resolved and added a
test with `fn` methods, which would also fail in compiled mode.
