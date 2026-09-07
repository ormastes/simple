# `math_abs(-3.0)` returns `0.0` on the interpreter path

- **Date:** 2026-08-08
- **Status:** OPEN
- **Area:** stdlib math / interpreter numeric lowering

## Symptom

`std.math.math_abs`, the f64 absolute-value function, returns `0.0` for a negative
input instead of the magnitude.

```
use std.math.{math_abs}
fn main():
    print("GOT=" + math_abs(-3.0).to_text())
```

```
GOT=0.0        # expected GOT=3.0
```

Measured on the Rust bootstrap seed's interpreter path against a tree pinned to
`origin/main`. `MATH_PI` from the same module renders correctly
(`GOT=3.141592653589793`), so the module loads and other symbols in it are fine —
this is specific to `math_abs`.

## Source

`src/lib/math.spl`:

```
fn math_abs(x: f64) -> f64:
    if x < 0.0:
        -x
    else:
        x
```

The body is a tail-expression `if`/`else` with a unary negation in one arm. Both
the unary-minus-on-f64 lowering and the tail-expression-as-return-value path are
candidates; `math_abs_i64` in the same file should be checked for the same shape.

## How it was found

Incidentally, while establishing a baseline for the `std.math` facade-shadowing
fix (`doc/08_tracking/bug/std_facade_shadows_tier_module_family_2026-08-08.md`).
It was first mistaken for re-export poisoning; probing the *unmodified* facade
showed `GOT=0.0` too, proving it pre-existing and independent of that change.

## Note

Recorded rather than fixed because it is a numeric-lowering defect unrelated to the
module-resolution work that surfaced it. It needs its own reproduction on the
pure-Simple binary (not just the seed) to determine whether the defect is in the
stdlib source or in the seed's interpreter.

## RESOLVED 2026-09-06 (Rust bootstrap seed) — tail-`if` merge slot was hardcoded `TypeId::I64`

**Status: FIXED in the Rust seed. Proven on the JIT (Cranelift) lane.** Header
`Status: OPEN` above is superseded by this section.

**Lane coverage, stated honestly.** The fix is in MIR lowering, so it is
backend-agnostic in principle (`MirLocal.ty` is what every backend reads), but
only the JIT lane was executed. The `native-build` lane could not be exercised
on this host: it fails with `native-capsule-receipt-invalid:_scratch.mabs3` for
BOTH the fixed seed and the unmodified deployed seed, i.e. a pre-existing
blocker unrelated to this change. The LLVM backend was not exercised either.

### Correction to the record above: wrong lane

The title and "Measured on the Rust bootstrap seed's interpreter path" are wrong
about the engine. `bin/simple run` defaults to the **JIT**; forcing the
tree-walking interpreter gives the RIGHT answer, and always did:

```
$ SIMPLE_EXECUTION_MODE=interpret .../simple run mabs2.spl
ABS_NEG=3.0                       # correct
$ env -u SIMPLE_EXECUTION_MODE .../simple run mabs2.spl    # JIT lane
ABS_NEG=0.0                       # wrong
```

So this is a MIR/codegen defect, not a stdlib or interpreter one.
`src/lib/math.spl` is correct as written.

### Reproduction, narrowed

Nothing to do with `abs`, unary minus, or `std.math`. The actual rule is: **a
tail-position `if`/`else` BLOCK in an f64-returning function yields `0.0`.**
Probe (`_scratch/mabs3.spl`, seed `bin/release/aarch64-unknown-linux-gnu/simple`,
JIT lane):

```
PLAIN=7.5          # fn -> f64:  7.5                     OK
RET=7.5            # fn -> f64:  return 7.5              OK
TAILIF_F64=0.0     # tail if/else BLOCK, f64 arms        WRONG (expected 7.0)
RETIF_F64=7.0      # if/else with explicit `return`s     OK
TAILIF_I64=7       # same shape, i64 arms                OK
TAILIF_TEXT=neg    # same shape, text arms               OK
```

An inline one-line tail `if` (`if c: 7.0 else: 8.0`) and an *assigned* block-if
(`val r = if c: ...`) are both correct — those go through `lower_if_expr`, which
already threads the real `expr_ty`. Only the STATEMENT form in tail position was
broken.

### Root cause

`SIMPLE_DUMP_MIR=tail_if_f64` showed the merge temp typed `TypeId(5)` = `I64`
while the parameter was `TypeId(11)` = `F64`:

```
  block BlockId(1)
    ConstFloat { dest: VReg(4), value: 7.0 }
    Store { addr: VReg(5), value: VReg(4), ty: TypeId(5) }    <-- I64 slot, F64 value
```

`HirStmt::If` lowering (`src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs`)
hardcoded `TypeId::I64` in four places: the `MirLocal` for `__if_merge_*`, both
arm `Store`s, and the merge-block `Load`. Downstream,
`codegen/instr/memory.rs::compile_store` derives the slot's Cranelift type from
`MirLocal.ty`, finds `I64` where the value is `F64`, matches **no** coercion arm
(it handles F32<->F64, I64->F32 and I64->F64, but not F64 into an I64 slot) and
falls through to `create_default` → `iconst(I64, 0)`. The float was replaced by
zero before it ever reached the return.

### Fix

Derive the merge slot type from the arms' HIR tail-value types
(`if_merge_local_ty` / `if_merge_tail_value_ty` in `lowering_stmt.rs`) instead of
hardcoding. Deliberately narrow: only `F32`/`F64` switch away from `I64`, and
only when every value-producing arm agrees on the same float type. Ints, bools,
text and heap values keep the historical `I64` slot, and arms that disagree keep
it too, so nothing else in the merge path moves. Recursion into nested tail `if`s
is depth-bounded (`IF_MERGE_TY_MAX_DEPTH`).

### Evidence

Before = deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`; after =
seed rebuilt from this fix. Same file, same JIT lane, `use std.math.{math_abs,
MATH_PI}`:

```
BEFORE  GOT=0.0   GOTP=0.0   PI=3.141592653589793
AFTER   GOT=3.0   GOTP=3.0   PI=3.141592653589793
```

Locked by four Rust regression tests in
`src/compiler_rust/compiler/src/mir/lower/tests/seed_regression_tests.rs`:
`tail_if_statement_merge_slot_is_f64_for_float_arms`, plus three that pin the
UNCHANGED `I64` behaviour for int, text, and mixed-type arms.

Widened after the first proof (`_scratch/mabs5.spl`, JIT lane, checked against
the interpreter as oracle): `elif` chains with f64 arms, tail `if`s nested
inside another tail `if`, and `f32` arms are all correct now and were all `0.0`
before.

### Still open

1. **Mixed-type arms are still broken** — one f64 arm and one integer-literal
   arm in an f64-returning function. Not a regression from this fix (identical
   before it); this fix deliberately left that shape on the old I64 slot because
   the repair belongs in HIR numeric coercion, not the merge slot. Filed as
   `doc/08_tracking/bug/tail_if_mixed_int_float_arms_lose_the_float_2026-09-06.md`.
2. The record's request for a reproduction on the **pure-Simple** binary is not
   answered here — this fix is in the Rust seed only. Whether
   `src/compiler/50.mir` carries the same hardcoded merge type has not been
   checked, and should be.
3. `native-build` / LLVM lanes not exercised (see the lane note at the top of
   this section).
