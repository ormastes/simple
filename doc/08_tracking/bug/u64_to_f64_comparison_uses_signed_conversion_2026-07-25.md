---
id: u64_to_f64_comparison_uses_signed_conversion_2026-07-25
status: OPEN
severity: high
discovered: 2026-07-25
discovered_by: Arduino UNO Q (QRB2210 / Cortex-A53) aarch64 board bring-up — cross-module result-u8 fixture returned rc=5 on real silicon
related: src/compiler/70.backend/backend/interpreter.spl
related: test/fixtures/native_crossmodule_result_u8/main.spl
related: scripts/check/check-cranelift-aot-aggregate-cross.shs
---

# Mixed `u64`/`f64` comparison converts the `u64` operand with a SIGNED int→float conversion

**Status:** OPEN. Reproduces on ALL execution paths — interpreter, x86_64 native
(cranelift, one-binary), and aarch64 native (cranelift, run on both qemu-aarch64
and a real Arduino UNO Q / Qualcomm QRB2210 Cortex-A53 board). This is NOT
aarch64-specific; it is a cross-backend front/middle-end semantics bug.

## Summary

When one operand of a comparison is an unsigned 64-bit integer (`u64`) whose
value has the high bit set (>= 2^63) and the other is a float, the compiler and
interpreter convert the `u64` to `f64` using a **signed** interpretation of its
bit pattern. So `0x8000000000000000u64` (= 2^63 = 9223372036854775808) is treated
as the double `-9223372036854775808.0` instead of `+9223372036854775808.0`, and
every mixed-type comparison against it is wrong.

## Repro

```simple
fn main() -> i64:
    val high: u64 = 0x8000000000000000u64   # 2^63, a POSITIVE number
    print("high_gt_0f={high > 0.0}")        # expected true  -> prints FALSE
    print("0f_lt_high={0.0 < high}")        # expected true  -> prints FALSE
    print("high_lt_bigf={high < 9223372036854775808.0}")  # expected false -> prints TRUE
    return 0
```

Observed (identical on interpreter, x86_64 native, aarch64 native on real board):
```
high_gt_0f=false      # WRONG (2^63 > 0 is true)
0f_lt_high=false      # WRONG
high_lt_bigf=true     # WRONG (2^63 < 2^63 is false)
high_le_bigf=true     # correct (coincidentally)
```

All four wrong results are exactly what you get if `high` is reinterpreted as the
signed value `-2^63`.

## Root cause

The int operand of a mixed int/float comparison is converted to `f64` without
carrying its unsigned-ness:

- **Interpreter** — `src/compiler/70.backend/backend/interpreter.spl`,
  `eval_gt`/`eval_gteq`/`eval_lt`/`eval_lteq` (lines ~729-973). `Value.Int(l)`
  stores a bare `i64` with no signedness tag, and the mixed arm does
  `Ok(Value.Bool(l.to_f64() > r))`. For a high-bit `u64`, `l` already holds the
  two's-complement pattern, so `l.to_f64()` yields the negative double.
- **Native (cranelift / LLVM)** — the MIR lowering for the int→float coercion at
  the comparison site emits a signed convert (`scvtf`-equivalent) rather than an
  unsigned convert (`ucvtf`) when the static operand type is unsigned.

A correct fix must thread the operand's static (un)signedness into the int→float
conversion at every comparison/arith-promotion site: interpreter `Value` must
know the int is unsigned (or the eval must consult the HIR operand type), and the
MIR/backends must select unsigned-convert for unsigned source types.

## Why it went unnoticed

`test/fixtures/native_crossmodule_result_u8/main.spl` exercises exactly this
(`if not (high > 0.0) or not (0.0 < high): return false` inside
`cross_target_arithmetic_ok`, returning exit code 5 on failure), but
`scripts/check/check-cranelift-aot-aggregate-cross.shs` only *runs* the fixture
when `CRANELIFT_CROSS_EXECUTE=1` (default 0); the routine CI path only checks that
it emits an object. So the runtime miscompile was never asserted.

## Impact

- Any Simple program comparing an unsigned 64-bit value >= 2^63 against a float
  gets the wrong answer — silently, on every backend.
- Surfaced during real-hardware bring-up: the cross-module fixture returned rc=5
  on the Arduino UNO Q board (and equivalently under qemu), which is otherwise a
  faithful, working aarch64 SimpleOS/Simple execution.

## Suggested fix + guard

1. Thread unsigned-ness into int→float conversion at comparison/promotion sites
   (interpreter + MIR lowering + native encoders).
2. Flip `CRANELIFT_CROSS_EXECUTE` on (or add a dedicated execution gate) so the
   result-u8 fixture's runtime result is asserted, not just its object emission.
