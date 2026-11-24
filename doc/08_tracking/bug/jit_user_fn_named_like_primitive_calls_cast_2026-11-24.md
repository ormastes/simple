# JIT called the `f32`/`i32` cast where the interpreter called a user `fn f32`

**Status:** FIXED on `work/compiler-jit-primitive-name-call-20261124`.
**Found:** 2026-11-24, while writing `compiler/tests/jit_parallel_codegen.rs`.
That test's generated functions were first named `f0..f119`, and `f32(17)`
summed differently.
**Regression spec:** `src/compiler_rust/compiler/tests/jit_user_fn_named_like_primitive.rs`.

## Repro (seed `run`)

```
fn f32(x: i64) -> i64:
    x + 1

fn i32(x: i64) -> i64:
    x + 2

fn main():
    print(f32(17))
    print(i32(17))
```

| mode | before | after |
|---|---|---|
| interpreter | `18`, `19` | `18`, `19` |
| JIT | `17.0`, `17` (the casts) | `18`, `19` |

## The rule

The language spec and syntax reference say nothing about built-in TYPE names as
function names. See
`builtin_type_name_shadowing_is_an_undecided_language_question_2026-08-22.md`,
which covers *type* declarations such as `struct text`. That question stays
open and is not touched here.

For *functions*, the interpreter's rule is already decided and tested:
- A module-level or imported `fn` wins over a builtin of the same name
  (`builtin_wins_over_user_fn`, `interpreter_call/mod.rs`).
- Only `PRELUDE_UNSHADOWABLE` (`exit`, `dprint`, `panic`) always reaches the
  builtin.
- History: `module_fn_shadowed_by_builtin_name_2026-08-21.md` and the
  `generator` precedent in `.claude/rules/language.md`.

The JIT now follows the same rule. None of the cast names is unshadowable.

## Root cause and fix

`lower_utility_builtin` (`hir/lower/expr/calls.rs`) turned every one-argument
call on a cast name (`i8..u64`, `f32`, `f64`, `int`, `float`, `bool`, `text`,
`str`, `String`, `char`) into a `Cast` before user functions were considered.

The fix skips the cast when `declared_function_returns` holds the name. That
map is filled before any body is lowered, for every module-level `fn` and every
imported free function. It works on both the flattened `run` lane and the
project lane; `own_declared_function_names` is empty on the flattened lane, so
it could not be used. A call with no user function of that name still lowers to
the cast. The spec checks both directions.
