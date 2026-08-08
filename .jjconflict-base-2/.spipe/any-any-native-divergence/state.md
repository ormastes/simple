# State: any+any native divergence fix

## Status: CLOSED — 2026-05-20

**Bug:** `any_plus_any_interpreter_native_divergence_2026-05-18.md`

## Investigation findings

### Interpreter path
`interpreter/expr/ops.rs` — `BinOp::Add` is a runtime match on `Value` variants:
- `(Value::Str, _)` or `(_, Value::Str)` → string concat
- `(Value::Int, Value::Int)` → arithmetic add

### Native path (before fix)
`mir/lower/lowering_expr_ops.rs` — `is_string_add` only triggers when one operand has
`TypeId::STRING`. When both have `TypeId::ANY`, it falls through to `MirInst::BinOp { iadd }`.

### Runtime value layout (confirmed from runtime_native.c)
Native `int64_t` values are **tagged**:
- Integers: `value << 3 | TAG_INT (0x0)` — raw `iadd` on tagged integers gives wrong results
  (adds tag bits; `1 + 2` as tagged = `(1<<3) + (2<<3) = 24`, not `3`)
- Strings: heap pointer `| TAG_HEAP (0x1)`
- Floats: `TAG_FLOAT (0x2)`
- Booleans/nil: `TAG_SPECIAL (0x3)`

Wait — re-reading: `TAG_INT = 0x0` means the bottom 3 bits are 0 for integers. So `iadd` on
two `TypeId::INT` tagged values `(1<<3) + (2<<3) = 24` — that's `3 << 3` which IS the tagged
representation of `3`. Actually `iadd` on TAG_INT=0 values works correctly because tag bits
cancel. So the integer `iadd` path is fine for pure integer ANY+ANY.

The real problem is `ANY + string` — if one arg is a string (heap-tagged pointer), `iadd`
produces garbage instead of string concatenation.

### Fix approach
When `left.ty == TypeId::ANY && right.ty == TypeId::ANY && op == Add`:
- Emit `MirInst::Call { rt_any_add(left, right) }` instead of `BinOp { iadd }`
- `rt_any_add` does runtime tag check: if either operand is a heap string, call
  `rt_string_concat`; otherwise do arithmetic `iadd` on de-tagged integers.

## Files changed
1. `src/runtime/runtime.h` — add `rt_any_add` declaration
2. `src/runtime/runtime_native.c` — implement `rt_any_add`
3. `src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs` — emit `rt_any_add` call
   for `ANY + ANY`

## Status: DONE
