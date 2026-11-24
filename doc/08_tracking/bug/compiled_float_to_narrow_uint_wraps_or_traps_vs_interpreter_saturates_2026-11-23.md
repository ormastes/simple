# Compiled float -> narrow int conversion wraps (or traps) where the interpreter saturates

- **Filed:** 2026-11-23
- **Class:** semantic divergence, seed Cranelift codegen (JIT `simple run` and
  native-build) vs. the interpreter oracle
- **Status:** fixed 2026-11-24 (work/compiler-numeric-conv-20261124). Was: found while verifying
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

## Resolution (2026-11-24)

**Decision: saturate.** The language docs say nothing on float -> int (the guides under
`doc/07_guide/language`, `doc/07_guide/quick_reference/syntax_quick_reference.md` and
`doc/04_architecture/language` do not cover it). So the reference engine wins. The
interpreter uses `semantics::cast_float_to_numeric` (`semantics/cast_rules.rs`) for both
`x as T` and `x.to_T()`, which is Rust `as`:
- it truncates toward zero;
- it saturates to the target width's range (`70000.5 -> u16` = 65535, `-5.5 -> u8` = 0,
  `1e20 -> i32` = 2147483647, +inf -> max, -inf -> min);
- NaN becomes 0.

The Rust seed's Cranelift engines (JIT `simple run` and native-build) now follow this rule.
Integer-source narrowing still wraps on every
engine, as before.

**Root cause.** All three Cranelift lowerings of a float -> int conversion did
`fcvt_to_{sint,uint}.i64` and then `ireduce`:
- `x as T`: `compile_cast`, `codegen/instr/basic_ops.rs`.
- `x.to_T()` / `to_int`: `compile_builtin_method`, `codegen/instr/methods.rs`, and
  `try_compile_builtin_method_call`, `codegen/instr/closures_structs.rs`.

`ireduce` WRAPS a value that fits in i64 but not in the target width. Cranelift's
non-saturating `fcvt_to_*` TRAPS (SIGILL on aarch64) on NaN, on values outside the i64/u64
range, and on any negative input to `fcvt_to_uint`. JIT and native-build share these
lowerings.

**Fix.** A new helper, `float_to_int_saturating` (`codegen/instr/helpers.rs`), does
`fcvt_to_{sint,uint}_sat.i64`, then clamps to the target range (`smin`/`smax`, or `umin`
for unsigned), then `ireduce`s. All three sites call it. Per conversion this adds two
integer ops in place of the trap checks.

**Not changed.**
- The implicit ABI adapters (`helpers.rs` float->int adapt, `body.rs` return of a float from
  an int-typed function, `calls.rs` argument adapt) still use trapping `fcvt_to_sint`. They
  are coercions, not user casts.
- The LLVM backend (`codegen/llvm/instructions.rs`, `emitter.rs`) still emits
  `fptosi`/`fptoui`, which give poison when out of range. It is behind the opt-in `llvm` cargo
  feature (`simple-compiler` default features are `[]`; the driver's default is only
  `alloc-mimalloc`), so the default seed does not include it.
- The self-hosted compiler's Cranelift adapter
  (`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`, `is_src_float and not
  is_dst_float`) deliberately TRAPS: plain `fcvt` traps on NaN, inf and I32/I64 overflow, and
  i8/i16 targets branch to an overflow block. That is a third behaviour. It needs an owner
  decision (saturate, to match the seed, or trap everywhere) and a self-hosted rebuild. It is
  not part of this seed fix.

**Evidence.** `src/compiler_rust/compiler/tests/float_to_int_saturating_cast_parity.rs` has
861 rows: 21 inputs (negative, fractional, the edges of each width, 1e19/1e20, +/-inf, NaN)
x 8 widths x 5 shapes (`x.to_T()`, `x as T`, call-result receiver, class-field receiver,
f32 source), plus `to_int`. The reference is the interpreter's own
`cast_float_to_numeric`. A second test runs the same rows in the interpreter.

| seed | JIT rows test | interpreter rows test |
|---|---|---|
| base `91681a19c8c` | CRASH (SIGILL, process killed) | pass |
| head | pass (861/861) | pass |

Probe program (13 inputs x 11 conversions, plus NaN/inf rows), head seed: interpreter, JIT
and native-build print identical values. The only text difference is native's `print` of
`1e30` itself (`1000000000000000019884624838656.0`); that is a float-formatting difference,
not a conversion one. Base: JIT and native both die with SIGILL (exit 132) on the first row.
