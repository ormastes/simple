# BUG: ANY+ANY semantic divergence between interpreter and native codegen

**Date:** 2026-05-18
**Severity:** Low (no known user-facing breakage)
**Related fix:** 5054eb144c — native `+` operator in non-main functions

## Problem

When both operands of `+` have `TypeId::ANY` (untyped function parameters), interpreter and native codegen behave differently:

- **Interpreter**: runtime dispatch — `1 + "x"` → string concat `"1x"`, `1 + 2` → arithmetic `3`
- **Native (Cranelift)**: always emits `iadd` — `1 + "x"` → garbage (integer add on pointer), `1 + 2` → correct `3`

## Root cause

The fix in `lowering_expr_ops.rs` removed `TypeId::ANY` from `is_string_add` to fix `+` in non-main functions. This was correct — `ANY` should NOT unconditionally route to `rt_string_concat`. But it means `ANY + ANY` now always becomes `iadd` in native mode.

## Impact

- **Current**: No known breakage. All stdlib `+` uses are on typed operands.
- **Future**: If users write `fn add(a, b): return a + b` and call with mixed types, interpreter and native will diverge.

## Proposed fix

Emit a runtime type-check branch for `ANY + ANY` in native codegen:
```
if is_string(left) || is_string(right):
  call rt_to_string(left), rt_to_string(right), rt_string_concat
else:
  iadd left, right
```

This requires runtime type tags, which may not be available in Cranelift AOT yet. Lower priority until polymorphic dispatch is needed in native mode.

## Workaround

Add type annotations to function parameters: `fn add(a: int, b: int)` or `fn concat(a: text, b: text)`.
