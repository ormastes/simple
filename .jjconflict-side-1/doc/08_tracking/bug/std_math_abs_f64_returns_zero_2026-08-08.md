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
