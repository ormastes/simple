# JIT calls the `f32`/`i32` cast where the interpreter calls a user `fn f32`

**Status:** OPEN. This is a silent wrong value: the JIT and the interpreter disagree.
**Found:** 2026-11-24, while writing `compiler/tests/jit_parallel_codegen.rs`.
That test's generated functions were first named `f0..f119`, and `f32(17)`
summed differently.

## Repro (seed `run`, any build since at least `7f5cb7077f0`)

```
fn f32(x: i64) -> i64:
    x + 1

fn i32(x: i64) -> i64:
    x + 2

fn main():
    print(f32(17))
    print(i32(17))
```

| mode | output |
|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | `18`, `19` (the user functions) |
| default / `jit` | `17.0`, `17` (the built-in casts) |

## Relation to the open language question

Whether a user declaration may shadow a built-in type name is still undecided:
`builtin_type_name_shadowing_is_an_undecided_language_question_2026-08-22.md`.
That decision does not change this bug. Whatever the rule turns out to be, both
execution modes must apply the same one. Today the interpreter lets the user
`fn` shadow the cast and the HIR/MIR (JIT) lane does not.

The fix is one of these:
- make the JIT resolve the user `fn` first, which matches the interpreter and
  the `generator` precedent; or
- reject the declaration in both modes.
