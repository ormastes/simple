# `[i8]` array literal reads back a wrong element value under the JIT

**ID:** i8_array_literal_reads_back_wrong_value_2026-08-17
**Date:** 2026-08-17
**Severity:** P2 — silent wrong value, no diagnostic. Narrower than the `[u64]`
copy defect because it needs an `[i8]` array, which is rare in this tree.
**Status:** OPEN — noticed and measured, not investigated.

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
