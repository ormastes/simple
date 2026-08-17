# `[i8]` array literal reads back a wrong element value under the JIT

**ID:** i8_array_literal_reads_back_wrong_value_2026-08-17
**Date:** 2026-08-17
**Severity:** P2 — silent wrong value, no diagnostic. Narrower than the `[u64]`
copy defect because it needs an `[i8]` array, which is rare in this tree.
Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

## Summary

An `[i8]` array literal does not read back the value that was written. Measured
under the cranelift JIT (`bin/simple run`):

```
i8   orig 43   copy 43   want 5
```

The source array was `[5i8, 6i8]`; element 0 reads as `43`.

## How it was found, and what it is NOT

Found while sweeping the element-type matrix for
`doc/08_tracking/bug/typed_array_variable_binding_zeroes_elements_2026-08-17.md`
(the `rt_array_copy` packed-layout defect). It is a **different** defect:

- That bug corrupted values during the *copy*, leaving the original intact.
- Here the **original is already wrong** before any copy happens, and the copy
  is faithful (`43 -> 43`).

So it is a construction or read-back problem in `[i8]` itself, not a copy
problem. It was deliberately left out of the `rt_array_copy` fix rather than
folded in, so neither change is evaluated on the other's evidence.

## Reproduction

```
fn si8() -> [i8]:
    [5i8, 6i8]

fn main():
    val i = si8()
    print i[0]      # prints 43, expected 5
```

Run with `SIMPLE_EXECUTION_MODE=jit bin/simple run <file>`.

## Investigation not yet done

- Whether the interpreter agrees (the matrix run that produced this line was
  JIT-only for the `[i8]` case; the other types were checked on both engines).
- Whether `43` is a stable function of `5` or incidental — one data point
  cannot distinguish a width/sign-extension bug from a wrong base pointer.
  Sweep several values before theorising.
- Whether `[i16]`/`[i32]` share it. The `[u64]` precedent shows these layouts
  are decided per element type, so neighbouring types must be measured, never
  assumed.

---

## ROOT CAUSE FOUND + FIXED (2026-08-17)

**Severity was under-stated: this is P1, not P2, and it is not about arrays.**
Every `i8` reaching the runtime value-boxing path was affected; `[i8]` was just
where it happened to be noticed.

### Answering the three open questions

- *Does the interpreter agree?* **No — the interpreter is CORRECT.** Measured on
  `bin/simple` (Rust seed): `SIMPLE_EXECUTION_MODE=interpreter` prints `5 6 7`
  for `[5i8,6i8,7i8]`; `=jit` prints `<special:43> <special:67> <special:59>`.
- *Is `43` a stable function of `5`?* **Yes.** `43 == (5 << 3) | 0b011`, i.e.
  the value tagged `TAG_SPECIAL` with the raw integer as its payload. The
  rendering is doubly-boxed, which is why the payload shown is itself already
  a tagged word.
- *Do `i16`/`i32` share it?* **No.** Measured: `i16`, `i32`, `u8`, `u16`, `u32`,
  `i64`, `u64` are all clean. **`i8` alone** is broken.

### The tell

```
val a: i8 = 0i8   ->  false
val a: i8 = 1i8   ->  true
val a: i8 = 3i8   ->  error
val a: i8 = 5i8   ->  <special:5>
```

`0`, `1`, `3` are `SPECIAL_NIL`/`SPECIAL_TRUE`/`SPECIAL_FALSE`/`SPECIAL_ERROR`
payload numbers. An i8 was being rendered *as a special value*, not as a number.

### Root cause

`TypeId::I8` and `TypeId::BOOL` **both lower to the cranelift machine type
`types::I8`** (`src/compiler_rust/compiler/src/codegen/types_util.rs:29-30`).
Five MIR lowering sites treated that machine-width coincidence as type identity
and routed `i8` through `rt_value_bool`, whose C signature is
`extern "C" fn rt_value_bool(b: bool)`
(`src/compiler_rust/runtime/src/value/sffi/value_ops.rs:23`). Passing an
arbitrary i8 payload into a Rust `bool` parameter is UB; in practice it produced
a `TAG_SPECIAL` word carrying the raw integer.

Sites, all of the form `x.ty == TypeId::BOOL || x.ty == TypeId::I8`:

| file | line (pre-fix) | boundary |
|---|---|---|
| `src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs` | 661 | builtin call arg (`print`) |
| `src/compiler_rust/compiler/src/mir/lower/lowering_expr_collection.rs` | 19 | tuple literal element |
| `src/compiler_rust/compiler/src/mir/lower/lowering_expr_collection.rs` | 239 | array `.push` element |
| `src/compiler_rust/compiler/src/mir/lower/lowering_expr_collection.rs` | 301 | array literal element |
| `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` | 584 | index expression |
| `src/compiler_rust/compiler/src/mir/lower/lowering_stmt.rs` | 664 | element assignment |

### Fix

At every site, `TypeId::I8` moved out of `needs_bool_boxing` and into
`needs_int_boxing` (so it emits `MirInst::BoxInt` like `i16`/`i32`/`u8`).
`bool` keeps `rt_value_bool`.

### Evidence

Reproducing probe/spec:
`test/01_unit/compiler/codegen/probe_i8_int_boxing_jit.spl` +
`test/01_unit/compiler/codegen/i8_int_boxing_repro_spec.spl`.
Similar-problem detection (all 8 integer widths x 4 erased-slot boundaries):
`test/01_unit/compiler/codegen/probe_int_width_boxing_matrix_jit.spl` +
`test/01_unit/compiler/codegen/int_width_boxing_matrix_class_spec.spl`.

The detection probe immediately caught a SEPARATE live defect the reproducer
could not see — see
`doc/08_tracking/bug/jit_tuple_get_returns_raw_tagged_word_to_i64_sink_2026-08-17.md`.
