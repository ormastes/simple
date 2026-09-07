# Tail `if` with one float arm and one integer arm loses the value (JIT)

- **Date:** 2026-09-06
- **Status:** OPEN
- **Severity:** P1 — silent wrong value, no diagnostic at any level
- **Area:** Rust bootstrap seed, MIR lowering of `HirStmt::If` / HIR numeric
  literal coercion
- **Lane:** JIT (Cranelift). The tree-walking interpreter is CORRECT.
- **Found:** while fixing
  `doc/08_tracking/bug/std_math_abs_f64_returns_zero_2026-08-08.md`. This is the
  residue that fix deliberately did NOT cover — it is not a regression from it;
  the shape was broken identically before.

## Symptom

A tail-position `if`/`else` **block** whose arms have *different* value types —
one f64, one integer literal — in an f64-returning function produces garbage.

```simple
fn mixed(x: i64) -> f64:
    if x < 0:
        1.5
    else:
        2

fn main():
    print("MIX_NEG=" + mixed(-1).to_text())
    print("MIX_POS=" + mixed(1).to_text())
```

Measured on the Rust seed, aarch64:

```
# JIT lane (default `run`)
MIX_NEG=0.0
MIX_POS=0.000...0001          # 322 digits: the integer 2 reinterpreted as f64 bits

# interpreter lane (SIMPLE_EXECUTION_MODE=interpret) — the oracle
MIX_NEG=1.5
MIX_POS=2
```

Both arms are wrong, in two different ways: the f64 arm is zeroed, the int arm
is bit-reinterpreted.

## Root cause

Same merge slot as the `math_abs` bug, one step further along.

`HirStmt::If` MIR lowering allocates one `__if_merge_*` temp local for the whole
`if`. Since 2026-09-06 its type is derived from the arms
(`if_merge_local_ty`, `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`),
but only when **every** value-producing arm agrees; disagreeing arms keep the
historical `TypeId::I64`. With an I64 slot:

- the `1.5` arm hits `compile_store`'s no-matching-coercion path and is replaced
  by `iconst(I64, 0)` → `0.0`;
- the `2` arm stores fine as an integer, and is then read back through an f64
  return → the bit pattern `2` read as an IEEE double, i.e. a denormal.

Choosing `F64` for the slot instead would not fix it: `compile_store`'s
`expected F64 / actual I64` arm is a **bitcast**, meant for f64 values carried
through an i64 cross-block variable — applied to a genuine integer it would turn
`2` into the same denormal. So the merge slot alone cannot express this; both
arms must be brought to one numeric type first.

## Where the fix belongs

HIR, not MIR: an integer literal in an arm of an `if` whose other arm is float
(or whose context demands float — here the function's declared `-> f64`) should
lower as a float literal, exactly as `val x: f64 = 2` presumably already does.
Once both arms carry `TypeId::F64`, the existing `if_merge_local_ty` picks the
F64 slot and the value survives with no further MIR change.

A MIR-side fallback is possible but worse: it would need a real `int -> float`
conversion instruction inserted per arm, duplicating type knowledge HIR already
has.

## Current pinned behaviour

`tail_if_statement_merge_slot_stays_i64_when_arms_disagree` in
`src/compiler_rust/compiler/src/mir/lower/tests/seed_regression_tests.rs` asserts
the I64 slot. That test documents the defect, it does not bless it — the HIR fix
must update it.

## Not affected

Agreeing-type arms are all correct as of 2026-09-06: f64/f64, f32/f32, i64/i64,
text/text, `elif` chains, and nested tail `if`s. Verified in `_scratch/mabs5.spl`
against the interpreter oracle.
