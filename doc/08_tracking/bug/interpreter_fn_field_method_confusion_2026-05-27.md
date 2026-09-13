## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: **RESOLVED** — Rust-side `evaluate_method_call_with_self_update` falls back to

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Bug: Interpreter conflates fn-typed field access with method calls

Status: **RESOLVED** — Rust-side `evaluate_method_call_with_self_update` falls back to

**Date:** 2026-05-27
**Severity:** Medium
**Component:** Interpreter (ref_interpreter)

## Symptom

```
error: semantic: method `handler` not found on type Route
```

When calling `r.handler(req)` where `handler` is a `fn(HttpRequest) -> HttpResponse` field (not a method), the interpreter treats it as a method call and fails.

## Reproduction

```simple
class Route:
    handler: fn(i32) -> i32

fn test():
    val r = Route(handler: \x: x + 1)
    r.handler(42)   # <-- interpreter says "method handler not found"
```

## Expected

Interpreter should resolve `r.handler` as field access yielding an fn value, then call it.

## Workaround

Extract to local: `val h = r.handler; h(42)`. Works but clutters call sites.

## Impact

Any class storing function-typed fields (callbacks, handlers, strategies) cannot use direct call syntax in interpreter mode.

## Status

**RESOLVED** — Rust-side `evaluate_method_call_with_self_update` falls back to
callable object fields (`Lambda` and `Function`) before reporting an unknown
method. Pure-Simple-side `eval_method_call` in `eval_ops_part1.spl` now also
falls back to `val_struct_get_field` + `val_is_function` before the error path.
Added `test/01_unit/compiler/interpreter/fn_field_call_spec.spl` to cover
`route.handler(41)` on a function-typed field.
