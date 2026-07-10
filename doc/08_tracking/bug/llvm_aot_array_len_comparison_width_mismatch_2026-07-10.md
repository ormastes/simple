# LLVM AOT Width Lookup and Array-Index Pointer Blocker

- **Date:** 2026-07-10
- **Status:** width mismatch fixed; array-index pointer definition still open
- **Area:** LLVM AOT lowering

## Summary

A tiny native `[u32]` probe exposed two width-loss paths in textual LLVM
lowering. Explicit MIR constants could inherit a stale local width, and
expression-style type lookups could return `nil` under bootstrap lowering.
The latter made declared `u32` comparison operands fall back to `i64`.

## Reproduction

The bounded CPU-SIMD span probe used:

```simple
if pixels.len() != (16 as i64): return 1
```

Before the fix, `native-build` failed in `llc-18` with:

```text
'%l20' defined with type 'i32' but expected 'i64'
%l21 = icmp ne i64 %l18, %l20
```

The fix makes explicit instruction types authoritative for constants and uses
explicit returns for local and operand type lookup. The focused MIR regression
now emits `icmp ne i32` for two declared `u32` operands and passes 3/3.

The final bounded AOT run no longer reports a width mismatch. It advances to a
separate array-index lowering failure:

```text
error: use of undefined value '%l15'
%0 = inttoptr i64 %l15 to ptr
```

The same span bridge passes interpreter tests. C runtime objects compile for
x86_64, AArch64, generic RISC-V, and RVV RISC-V. The three-cycle AOT retry cap
was reached, so the undefined array-index pointer is retained as the remaining
native probe blocker rather than retried in this session.

## Separate Signedness Hazard

This width fix does not change ordered integer predicates. LLVM lowering still
uses signed `slt`/`sle`/`sgt`/`sge` predicates after erasing `u32` signedness to
`i32`, and `i32` widening still selects `sext`. That existing semantic gap needs
signedness-preserving MIR metadata and a dedicated regression; it is not part
of the equality/inequality width fix above.

## Expected

Array-index pointer locals must be defined before the generated `inttoptr`.
After that independent defect is fixed, the focused span probe should compile
and execute without changing its comparison semantics.
