# JIT: float/text pushed through an `[any]` function into an `[i64]` reads back as garbage

- Date: 2026-10-20
- Status: open (pre-existing; found while checking the #3989 revert)
- Binary: deployed Rust seed `bin/simple` (built 2026-10-20 16:37, no `rt_typed_words_i64_*` symbols, so unrelated to #3989)

Reproducer: `test/01_unit/compiler/jit_any_writer_into_i64_array_probe.spl`
(only small values, so nothing is wide or packed):

```
SIMPLE_EXECUTION_MODE=jit bin/simple run test/01_unit/compiler/jit_any_writer_into_i64_array_probe.spl
```

JIT prints `x4=2996075313569` and `x5=2996075474753` (pointer-like garbage) for
the pushed `1.5` and `"hi"`. The interpreter prints `x4=1.5`, `x5=hi`. A `nil`
set through the `[any]` function reads back correctly.

Cause (suspected): the JIT lowers `a.push(v)` on a value statically typed `[i64]`
at the call site as an integer push and does not box/tag the erased `any` value.
Not yet investigated.
