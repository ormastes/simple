# Bug: Free-function generic `T?` return wraps values in `Option::Some`

**Date:** 2026-06-26  
**Severity:** P2 — affects usability of generic helper free functions  
**Status:** Workaround applied; interpreter fix pending

## Summary

In the seed interpreter (and STAGE4), a top-level free function with a generic
optional return type `T?` always wraps its return value in `Option::Some(value)`
instead of returning the raw value.  Returning `nil` produces `Option::None`
instead of actual nil.  `impl`-method `T?` returns are **not** affected — they
work correctly.

## Reproduction

```spl
struct Box<T>:
    item: T

impl Box<T>:
    fn get() -> T?:     # method — returns raw 42 ✓
        me.item

fn box_get<T>(b: Box<T>) -> T?:   # free fn — returns Option::Some(42) ✗
    b.item

val b = Box(item: 42)
expect(b.get()).to_equal(42)        # passes
expect(box_get(b)).to_equal(42)    # fails: expected Option::Some(42) to equal 42
```

## Affected Files

- `src/lib/tooling/ds_utils.spl` — `stack_get` and `queue_get` worked around
  with `any` return type (see ponytail comments in that file).

## Workaround

Change affected free functions from `T?` to `any`.  The caller's `to_equal` and
`to_be_nil` matchers work correctly against `any`.  Loses static type info but
preserves runtime behaviour.

## Fix Location

Likely in the interpreter's function-return handling for generic optionals.
Compare `eval_fn_return` for methods vs free functions — the method path
correctly unwraps/passes through while the free-function path wraps in
`Option::Some`.

See `src/compiler_rust/` interpreter eval code.
