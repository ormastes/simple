# Seed JIT miscompiles wide i64 literals (`0x7FFFFFFFFFFFFFFF` → `-1`)

**Status:** open
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane J, while proving the
`XlenConfig.mask` fix)
**Area:** Rust seed JIT (cranelift lane) — constant materialization of wide i64
literals
**Severity:** high — silent wrong values for any 64-bit constant near the i64
boundary; the interpreter is correct, so the divergence is mode-dependent and easy
to miss

## Finding

Under the seed **JIT**, wide i64 literals evaluate to wrong values; under the seed
**interpreter**, the same expressions are correct:

| Expression | Interpreter (correct) | Seed JIT |
|---|---|---|
| `0x7FFFFFFFFFFFFFFF` | `9223372036854775807` (i64::MAX) | **`-1`** |
| `9223372036854775807` | `9223372036854775807` | **`-1`** |
| `(1 << 63) - 1` | `9223372036854775807` | **`-1`** |
| `0x8000000000000000` | `-9223372036854775808` (i64::MIN) | **`0`** |
| `0xFFFFFFFFFFFFFFFF` | `-1` (all-ones, wraps) | (see repro) |

Three distinct spellings of i64::MAX all collapse to `-1`, and i64::MIN collapses
to `0`. This is consistent with a constant-materialization defect (e.g. a boxed-int
or sign-extension path truncating the high bit), not a parser issue — the
interpreter proves the frontend reads the literals correctly.

## Relation to the known 61-bit boxed-int defect

`doc/08_tracking/bug/seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`
documents the seed JIT dropping high bits of full-64-bit values held in **array
state** (sim-only). This finding shows the same *class* of defect for **plain
literals in scalar expressions** — no arrays involved. Whether it is the same root
cause or a sibling is undetermined; if the 61-bit tag-box is the cause, values with
bits 61-63 set would all be suspect, matching the observed pattern.

## Impact

- Any RV64 model arithmetic relying on boundary constants (`i64::MAX`, `i64::MIN`,
  all-ones masks, `mcause` interrupt bit `0x8000000000000000`) is silently wrong
  under JIT. The hardware tree hits this pattern repeatedly:
  `rv64gc_rtl/{alu,atomics,core_helpers,imac_helpers}.spl` all use
  `val flip: i64 = 0x8000000000000000`.
- This is why the interpreter-only rule for rv64 models exists; the rule is hereby
  re-confirmed for *scalar literal* code, not just array state.
- Tests that pass under `bin/simple run` (JIT) with these constants may be
  asserting on wrong values that happen to match wrongly-computed expectations —
  an equality-is-not-correctness trap.

## Reproduction

```bash
cd /home/ormastes/dev/pub/simple
cat > /tmp/widelit.spl <<'EOF'
fn main():
    val a: i64 = 0x7FFFFFFFFFFFFFFF
    val b: i64 = 0x8000000000000000
    print "{a} {b}"
EOF
bin/simple run /tmp/widelit.spl                                  # JIT: wrong
SIMPLE_EXECUTION_MODE=interpreter bin/simple run /tmp/widelit.spl  # correct
```

## Suggested fix

Trace the JIT's i64 constant materialization for values with bit 61+ set; add a
codegen test asserting the five expressions above equal their interpreter values.
Cross-check against the 61-bit boxed-int bug to determine shared root cause.

## Related

- `doc/08_tracking/bug/seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`
- `doc/08_tracking/bug/jit_option_i64_value3_none_collision` (same family:
  JIT value-representation collisions)
- Campaign plan: `doc/03_plan/agent_tasks/simple_riscv_hardening_2026-07-27.md`
