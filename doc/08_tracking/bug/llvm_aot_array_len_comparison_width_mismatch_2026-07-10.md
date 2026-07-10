# LLVM AOT Array-Length Comparison Width Mismatch

- **Date:** 2026-07-10
- **Status:** open
- **Area:** LLVM AOT lowering

## Summary

A tiny native probe that compares `[u32].len()` with an integer constant fails
before linking because LLVM receives an `icmp ne i64` whose constant operand is
defined as `i32`.

## Reproduction

The bounded CPU-SIMD span probe used:

```simple
if pixels.len() != (16 as i64): return 1
```

`native-build --runtime-bundle core-c` fails in `llc-18` with:

```text
'%l20' defined with type 'i32' but expected 'i64'
%l21 = icmp ne i64 %l18, %l20
```

The same span bridge passes interpreter tests. C runtime objects compile for
x86_64, AArch64, generic RISC-V, and RVV RISC-V. The three-cycle AOT retry cap
was reached, so no further expression rewrites were accepted as native proof.

## Expected

Integer casts and inferred constants used against `array.len()` must lower to
the same LLVM width. The focused span probe should compile without changing its
comparison semantics.
