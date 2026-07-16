# Native: `"{a() and b()}"` interpolation fails llc (ptr vs i64 type mismatch)

**Status:** Open  **Found:** 2026-07-16 (p_shortcircuit lane)  **Path:** native-build --entry (strict-llvm)
```simple
fn t() -> bool:
    return true
fn main() -> i64:
    print("v={t() and t()}")   # build fails: llc exit 1
    return 0
```

`llc-18: '%lNN' defined with type 'ptr' but expected 'i64' — %t5 = inttoptr i64 %lNN to ptr`

## Notes

- PRE-EXISTING at base de7cb5a238a: reproduces identically with and without the
  p_shortcircuit Bool-result fix for the And/Or lowering (only the local number
  shifts, `%l18` pre / `%l20` post), so it is not caused by that change.
- A logical `and`/`or` result used in a string interpolation slot routes
  through `coerce_concat_operand` (expr_dispatch.spl); some operand along that
  chain ends up `ptr`-typed where the emitter expects `i64`, producing an
  invalid `inttoptr` whose source is already a pointer.
- LOUD failure (build error), not silent-wrong output. Plain `print(a and b)`,
  `if`/`while` conditions, `val` bindings, and nested `and`/`or` all build and
  run correctly with the short-circuit lowering + Bool-result fix.

## Repro

`env -u SIMPLE_BOOTSTRAP -u SIMPLE_RUNTIME_PATH SIMPLE_NO_STUB_FALLBACK=1 bin/simple native-build --entry <case>.spl -o <bin> --clean`
