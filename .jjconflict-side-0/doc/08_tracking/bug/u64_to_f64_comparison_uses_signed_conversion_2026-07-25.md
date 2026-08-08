---
id: u64_to_f64_comparison_uses_signed_conversion_2026-07-25
status: FIXED
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

## Fix status (2026-08-06 verification pass)

**Interpreter (pure Simple) — FIXED, verified.**
`src/compiler/70.backend/backend/interpreter.spl` now has a dedicated
`interp_int_to_f64(bits: i64, is_unsigned: bool) -> f64` helper (~line 55) that
reinterprets a negative `i64` bit pattern as the correct unsigned `f64` when the
operand's static type is unsigned (splits off the top bit: `9223372036854775808.0
+ (bits & 0x7FFFFFFFFFFFFFFF).to_f64()`). Every mixed int/float site —
`eval_gt`/`eval_gteq` (~line 797/818) and the inline `HirBinOp.Lt`/`HirBinOp.LtEq`
arms of `eval_binop` (~line 999/1026), plus `Add`/`Sub`/`Mul`/`Div` promotion —
now calls `interp_int_to_f64(l, left_unsigned)` / `interp_int_to_f64(r,
right_unsigned)` instead of a bare `.to_f64()`. The unsigned flag is threaded in
via `left_unsigned`/`right_unsigned` parameters resolved from the HIR operand's
static type (`interp_hir_expr_unsigned`, ~line 65), not from the untagged
runtime `Value.Int`. This is already merged to `origin/main` (commit
`969c1f013c38bbb6f9f2e8235d051fe57b83488b`, landed 2026-08-05 08:26 UTC by a
prior session) — this verification pass confirmed correctness by code audit and
did not need to author a new interpreter change.

**Native / MIR lowering (pure Simple `src/compiler/`) — FIXED, verified.**
`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` (comparison-lowering
arm, ~line 2838) now consults both the MIR local's static type and the HIR
operand's static type (`hir_expr_static_unsigned`, ~line 88) and, when the
operand is statically unsigned, retypes it to `MirType(kind: MirTypeKind.U64)`
*before* casting to `f64`, so the backend's `Cast` lowering (which keys off the
source operand type) selects the unsigned convert (`uitofp`/`fcvt_from_uint`)
instead of the signed one. Already merged to `origin/main` (commit
`cfe0506e336bb4af8c40e6b212c9c15d9bdd252e`, landed 2026-08-05 07:24 UTC by a
prior session).

**Verification method and honest limitations.** A full self-hosted `run`/`test`
capable binary built from a worktree at/after both fix commits was not available
in this pass, and building one is a T2/T3-scope operation (full/large
bootstrap) that this pass's constraints explicitly avoided. Verification was
therefore:
- Source audit of both fixed sites above (logic confirmed correct by hand).
- The pre-existing dedicated regression spec
  `test/01_unit/compiler/u64_to_f64_comparison_spec.spl` already encodes the
  doc's exact repro plus additional cases (2^63, 2^63+1, u64::MAX, mixed
  arithmetic, and a negative-i64 control group) and matches the fixed logic.
- Empirical A/B on Rust-seed binaries as corroborating (not primary) evidence:
  a stale seed build (`build/native_probe/simple`, 2026-07-23) reproduces the
  original bug exactly as described (`false, false, true, true, false` for the
  doc's five assertions), while the currently-deployed release seed
  (`bin/release/x86_64-unknown-linux-gnu/simple`, rebuilt 2026-08-05 11:01 UTC)
  gives the fully correct result (`true, true, false, true, true`) both under
  default JIT and under `SIMPLE_EXECUTION_MODE=interpret`. Note this exercises
  the Rust seed's own interpreter (which carries unsigned-ness via a distinct
  `Value::UInt` runtime variant in `src/compiler_rust/compiler/src/value_impl.rs`
  — a structurally different mechanism from the pure-Simple `interpreter.spl`
  fix) — it is suggestive that the bug is resolved end-to-end but is not a
  direct execution of the changed `.spl` file.
- `bin/simple test test/01_unit/compiler/u64_to_f64_comparison_spec.spl` was
  attempted but was **not usable as evidence**: it silently delegates to a
  separate, stale Rust *debug* seed child
  (`src/compiler_rust/target/debug/simple`, confirmed via the runner's own
  `child binary:` log line) which fails even the unrelated negative-i64 control
  case in the same spec — i.e. that child binary is generally stale/broken, not
  a signal about the pure-Simple fix under test. This matches the known
  "`simple test` silently delegates to seed child" pitfall.
- A native-build execution attempt through a same-day self-hosted stage3
  artifact from another session's scratch build
  (`build/bootstrap-agent-mirtype-20260805/stage3/.../simple`, built 2026-08-05
  10:15 UTC, i.e. after both fix commits) core-dumped on this fixture
  independent of the u64/f64 logic (likely a runtime-path/linking issue with
  that scratch artifact, not a regression from this fix) — inconclusive, not
  used as evidence either way.

**Net status:** both the interpreter and the pure-Simple native/MIR-lowering
sides of this bug are FIXED in source and already on `origin/main`. The
still-open gap is the CI assertion gap noted above (`CRANELIFT_CROSS_EXECUTE`
default-off, so the cross-module fixture's *runtime* result still isn't gated)
and the Rust-seed (`src/compiler_rust`) cranelift/LLVM native path, which this
pass did not audit or touch (out of scope; the current deployed seed *empirically*
gives correct answers per the A/B above, but its native/AOT codegen path was not
independently source-audited the way the two pure-Simple sites were).
