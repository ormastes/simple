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

## Expected

Interpreter should allow field mutation in non-`val` method context, same as compiled mode.

## Workaround

Use factory constructors or return new instances. Not acceptable for mutable APIs (e.g., `router.set_not_found(handler)`).

## Impact

Blocks interpreter-mode usage of any class with mutable state (HTTP server, routers, connection pools).
