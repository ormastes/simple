# BUG: ANY+ANY semantic divergence between interpreter and native codegen

**Date:** 2026-05-18
**Status:** FIXED — commit `e533e54c0b` (2026-05-19)
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

## Fix (e533e54c0b, 2026-05-19)

Three-part change:

1. **`src/runtime/runtime.h`** — declared `rt_any_add(int64_t left, int64_t right) -> int64_t`
2. **`src/runtime/runtime_native.c`** — implemented `rt_any_add`: checks whether either operand
   is a heap-tagged string via `rt_core_as_string`; if so, delegates to `rt_string_concat`;
   otherwise returns `left + right` (integer arithmetic on tag-zero INT values is safe because
   TAG_INT=0x0 so tag bits cancel under addition).
3. **`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`** — when
   `op == BinOp::Add && left.ty == TypeId::ANY && right.ty == TypeId::ANY`, emits
   `MirInst::Call { rt_any_add }` before the `is_string_add` block instead of falling through
   to `MirInst::BinOp { iadd }`.

The interpreter path (`ops.rs` L631–L664) already dispatches correctly by matching on
`Value::Str` at runtime; the fix brings native codegen to parity.

### Residual gap: ANY+STRING / STRING+ANY (one typed, one untyped)

The `is_string_add` block (L65–L107) fires when at least one operand is `TypeId::STRING`.
When `left.ty == TypeId::ANY` and `right.ty == TypeId::STRING`, the string-concat path is
taken (correct). However `left.ty != TypeId::STRING && left.ty != TypeId::ANY` is `false`
for the ANY case, so `rt_to_string` is NOT called on the ANY side — it is passed raw to
`rt_string_concat`. This is safe as long as `rt_string_concat` handles non-string first
arguments, but it may produce unexpected coercion behaviour. Lower priority; no regression
from prior state.

## Workaround (pre-fix)

Add type annotations to function parameters: `fn add(a: int, b: int)` or `fn concat(a: text, b: text)`.
