# Seed JIT miscompiles wide i64 literals (`0x7FFFFFFFFFFFFFFF` → `-1`)

**Status:** open
**Found:** 2026-07-27 (Simple RISC-V hardening campaign, Lane J, while proving the
`XlenConfig.mask` fix)
**Area:** Rust seed JIT (cranelift lane) — ~~constant materialization of wide i64
literals~~ **boxing of wide i64 values into tagged slots** (see the 2026-08-17
mechanism correction at the bottom; the title and this line are both wrong about
the mechanism, and the wrong mechanism sent at least one lane to the constant
materialization code, which is not defective)
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

---

## 2026-08-17 — mechanism correction + COLLAPSE with two other docs

Re-reproduced on the deployed seed (`bin/release/x86_64-unknown-linux-gnu/simple`,
mtime 2026-08-16 22:59). The doc's repro still fails exactly as filed:

```
$ bin/simple run w2.spl                       # JIT
-1 0
$ SIMPLE_EXECUTION_MODE=interpret bin/simple run w2.spl
9223372036854775807 -9223372036854775808
```

**But it is NOT constant materialization.** The discriminator the original filing
missed: printing the same values WITHOUT interpolation is already correct on the
JIT.

```
val a: i64 = 0x7FFFFFFFFFFFFFFF
print(a)          # JIT: 9223372036854775807  <- CORRECT
print "{a}"       # JIT: -1                   <- WRONG
```

The literal is materialized correctly. The corruption happens when the value is
BOXED into a tagged slot, which `{a}` does and `print(a)` does not.

**Root cause (shared).** The inline boxed-integer form is `v << 3` with a 3-bit
tag, i.e. a 61-bit SIGNED payload. `|v| >= 2^60` shifts its top bits out and the
matching `>> 3` sign-extends a different number back.

**This collapses three separately-filed docs into one defect:**

| doc | reported symptom | same arithmetic |
|---|---|---|
| this one | `"{i64::MAX}"` -> `-1` | `(2^63-1) << 3 >> 3` |
| `seed_jit_spl_f64_to_bits_miscompile_2026-07-23.md` | `[i64]` readback of `0x4008000000000000` -> `2251799813685248` | `(0x4008000000000000 << 3) mod 2^64 >> 3` = 2251799813685248 **exactly** |
| `untyped_list_element_read_seed_rootcause_2026-07-30.md` | `: list` element read -> `value*8` | the DECODE half — no unbox emitted at all |

Verified arithmetic, not conjecture: 0x4008000000000000 * 8 mod 2^64 =
0x0040000000000000; >> 3 = 2251799813685248, the exact number that doc reports.

**Codegen side is already fixed and committed.** Both Cranelift `BoxInt` sites
route through `rt_value_int` rather than emitting a raw `ishl 3`
(`src/compiler_rust/compiler/src/codegen/instr/mod.rs:1448`, with the
int61-truncation rationale in the comment above it). The remaining gap was on the
RUNTIME side, in `rt_value_int`'s own encode/decode.

**Fences added (this session):**
- `test/01_unit/compiler/codegen/probe_wide_int_box_roundtrip.spl` — run-path
  probe, six boundaries (interpolation, `[i64]` element, extern return, nullable
  `i64?`, struct field, untyped `list` param) x five magnitudes, every oracle an
  absolute literal.
- `test/01_unit/compiler/codegen/wide_int_box_roundtrip_class_spec.spl` — drives
  that probe as a SUBPROCESS under both engines. A spec body runs interpreted,
  and the interpreter is correct for this whole class, so an in-process example
  can never go red on it.

The class probe is strictly stronger than either original reproducer: on the
deployed seed it reports **9 FAIL lines** (array max/min/+2^60/fbits, extern
readback, extern equality, optional max/min, list-param small/max) where the two
docs reported one case each. Notably `field_i64_max` PASSES — the struct-field
path was already correct — which is why single-site reproducers kept missing the
shape.
