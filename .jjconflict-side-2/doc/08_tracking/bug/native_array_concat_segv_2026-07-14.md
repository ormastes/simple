# Native: array + concat (a + [x]) SIGSEGVs

**Status:** Resolved 2026-07-15  **Found:** 2026-07-14 (iterators lane)  **Path:** native-build --entry
```simple
fn main():
    val a = []
    val b = a + [2, 4]
    print(b.len())   # was: native SIGSEGV (139); now: prints 2 == oracle
```
No loops involved. Array `+` concat lowering (binop / aggregate) crashed.

## Root cause

`Binary(Add)` lowering in `expr_dispatch.spl` only special-cased string
operands (`bin_is_str_concat`). An array-typed operand (heap `SplArray*` handle)
fell through to the generic `emit_binop(Add)`, integer-adding the two pointer
bit patterns → garbage pointer → SIGSEGV on first deref.

## Resolution

`e9165c53a667` (exprdispatch2 lane): added a parallel `bin_is_array_concat`
branch keyed on `local_is_runtime_array` that calls the pre-existing
`rt_array_concat` runtime helper. The `FuncPtr` signature uses the resolved
array result type for params + return (per the verified `rt_array_repeat`
precedent) so the emission does not diverge between the `i64` and `ptr` sites.
No `aggregate_intrinsics.spl` change was needed — the concat result flows
through the generic `emit_call`.

Verified native == oracle for `[] + [2,4]` (2), chained `a + [3,4] + [5]` (5),
and element access. Parity harness case `array_concat` is green in the
`check-native-seed-parity.shs` gate.
