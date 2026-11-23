# Compiled float -> narrow int conversion wraps (or traps) where the interpreter saturates

- **Filed:** 2026-11-23
- **Class:** semantic divergence, seed Cranelift codegen (JIT `simple run` and
  native-build) vs. the interpreter oracle
- **Status:** open. Not fixed; found while verifying
  `native_call_result_f64_to_int_conversion_bits_2026-11-23.md`, and not caused
  by that fix (the base seed behaves the same).

## Repro

```simple
fn main():
    val x: f64 = 70000.5
    print(x.to_u16())            # interpreter 65535, compiled 4464
    print((x as i64).to_u16())   # 4464 everywhere (integer source wraps)
    print((-5.5).to_u8())        # interpreter 0, compiled: SIGILL (exit 132)
```

Measured 2026-11-23 on aarch64 (GB10 host):

| row | interpreter | JIT (`run`) | native-build |
|---|---|---|---|
| `70000.5.to_u16()` | 65535 | 4464 | 4464 |
| `(70000.5 as i64).to_u16()` | 4464 | 4464 | 4464 |
| `(-5.5).to_u8()` | 0 | SIGILL | SIGILL |

Seeds: `/home/yoon/.cache/f64conv-bins/simple.base` (release/1.0.0
`0d8f4d2e22e`) and `simple.fixed` (same plus the call-result decode) give
identical compiled results.

## Cause (located, not fixed)

The interpreter saturates a float source into the target range. The seed cast
lowering (`compile_builtin_method` in `codegen/instr/methods.rs`,
`try_compile_builtin_method_call` in `codegen/instr/closures_structs.rs`)
converts float -> i64 with `fcvt_to_sint` / `fcvt_to_uint` and then `ireduce`s,
so an in-i64-range but out-of-target-range value wraps (70000 mod 65536 = 4464).
For an unsigned target it uses `fcvt_to_uint`, which TRAPS on a negative input
(Cranelift traps on out-of-range/NaN), hence the SIGILL.

## Needed decision / fix

Pick one semantics for float -> narrow int (`to_u8/u16/u32/i8/i16/i32`) and make
every engine follow it. The interpreter (the reference engine) saturates; the
compiled lowering would then use `fcvt_to_*_sat` to the target width (or
saturate the i64 result to the target range) instead of `fcvt` + `ireduce`.
Integer-source narrowing (wrap) is consistent across engines and is not part of
this bug.
