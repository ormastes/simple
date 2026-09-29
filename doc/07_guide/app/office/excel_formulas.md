# Excel Formulas in Simple Sheets

Audience: users writing spreadsheet formulas in `src/app/office/sheets`, and
developers extending the formula engine.

Companion guides:
- `doc/07_guide/app/office/writing_calc_functions.md` — how to add a new function
- `doc/07_guide/app/office/excel_to_math_migration_guide.md` — the migration record

## Where the math actually comes from

Excel formula functions do **not** carry their own numeric implementations.
Every trigonometric, logarithmic, exponential and root function in
`src/app/office/sheets/formula.spl` dispatches through the adapter module
`src/app/office/sheets/math_bridge.spl`, which in turn delegates to the
standard library under `std.common.math` (plus the SFFI wrappers in
`std.nogc_sync_mut.io.math`).

```
formula.spl  ──dispatch──▶  math_bridge.spl  ──delegate──▶  std.common.math.*
   "SIN(x)"                    excel_sin(x)                    math_sin(x)
```

The bridge exists so that Excel-facing error semantics (`#ERR` on a domain
violation, Excel's `TAN` overflow behaviour, `SQRTPI`'s implicit π factor) stay
in the spreadsheet layer, while the numerics stay in one place in the stdlib.
Domain validation lives at the dispatch site in `formula.spl`; bridge functions
are pure `f64 -> f64` and assume a validated argument.

## Function map

### Trigonometry

| Formula | Bridge wrapper | stdlib target |
|---|---|---|
| `SIN(x)` | `excel_sin` | `math_sin` |
| `COS(x)` | `excel_cos` | `math_cos` |
| `TAN(x)` | `excel_tan` | `math_sin` / `math_cos` (returns Excel's infinity at a cosine zero) |
| `ASIN(x)` | `excel_asin` | `math_asin` |
| `ACOS(x)` | `excel_acos` | `math_acos` |
| `ATAN(x)` | `excel_atan` | `math_atan` |
| `ATAN2(x, y)` | `excel_atan2` | `math_atan2` |
| `DEGREES(x)` | `excel_degrees` | `MATH_PI` |
| `RADIANS(x)` | `excel_radians` | `MATH_PI` |

`ASIN` and `ACOS` are the non-trivial cases: they are defined only on
`[-1, 1]`, and the endpoints are exact. `ASIN(1)` is exactly `MATH_PI / 2`
(`1.5707963267948966`) and `ACOS(1)` is exactly `0.0`. `formula.spl` rejects
arguments outside `[-1, 1]` before the wrapper is ever called.

### Hyperbolic

| Formula | Bridge wrapper | Identity used |
|---|---|---|
| `SINH(x)` | `excel_sinh` | `(e^x - e^-x) / 2` via `math_exp` |
| `COSH(x)` | `excel_cosh` | `(e^x + e^-x) / 2` via `math_exp` |
| `TANH(x)` | `excel_tanh` | `(e^2x - 1) / (e^2x + 1)` via `math_exp` |

### Logarithmic, exponential and roots

| Formula | Bridge wrapper | stdlib target |
|---|---|---|
| `LN(x)` | `excel_ln` | `ln_f64` (`std.common.math.special`) |
| `LOG10(x)` | `excel_log10` | `ln_f64(x) / ln_f64(10)` |
| `LOG(x, base)` | `excel_log` | `ln_f64(x) / ln_f64(base)` |
| `EXP(x)` | `excel_exp` | `math_exp` |
| `SQRT(x)` | `excel_sqrt` | `math_sqrt` |
| `SQRTPI(x)` | `excel_sqrt_pi` | `math_sqrt(MATH_PI * x)` |
| `POWER(b, e)` | `excel_power` | `math_pow` |

Domain errors are raised by the dispatcher, not the bridge: `LN(0)`,
`LOG10(0)`, `SQRT(-1)` and `SQRTPI(-1)` all return an Excel error value
without entering the wrapper.

### Aggregates and rounding

`excel_sum`, `excel_average`, `excel_count`, `excel_min`, `excel_max`,
`excel_product`, `excel_sumsq`, `excel_stdev`, `excel_var`, `excel_median`,
`excel_roundup`, `excel_rounddown`, `excel_round`, `excel_trunc`,
`excel_even`, `excel_odd`, `excel_mround`, `excel_floor`, `excel_ceiling`,
`excel_standardize`, `excel_stdev_p` and `excel_var_p` cover the aggregate and
rounding surface. The statistical ones delegate to
`std.common.math.statistics` (`mean`, `median`, `stdev_sample`, `var_sample`,
`stdev_pop`, `var_pop`, `standardize`).

## Using the same functions from a Simple script

Everything the spreadsheet uses is ordinary stdlib, so a script gets identical
results without going through the formula engine:

```simple
use std.common.math.math.{math_sin, math_sqrt, MATH_PI}
use std.common.math.statistics.{mean}

fn main():
    print(math_sin(MATH_PI / 2.0))     # 1.0, same as =SIN(PI()/2)
    print(math_sqrt(16.0))             # 4.0, same as =SQRT(16)
    print(mean([1.0, 2.0, 3.0, 4.0]))  # 2.5, same as =AVERAGE(A1:A4)
```

This is the point of the migration: a formula and a script that compute the
same thing now run the same code.

## Extending

To add a formula that needs new numerics:

1. Add or reuse the numeric function in `src/lib/common/math/`.
2. Add a thin Excel-semantics wrapper in `math_bridge.spl`.
3. Add the dispatch case (with its domain validation) in `formula.spl`.
4. Add a spec under `test/01_unit/app/office/sheets/`.

Do not add a private numeric helper to `formula.spl` — the duplicated
`_sin_f64`, `_cos_f64`, `_atan_f64`, `_sqrt_f64` helpers and the `_PI` constant
were removed for exactly that reason.

## References

- `src/app/office/sheets/formula.spl` — dispatch and domain validation
- `src/app/office/sheets/math_bridge.spl` — Excel-semantics wrappers
- `src/lib/common/math/` — `math.spl`, `statistics.spl`, `special.spl`,
  `distributions.spl`, `financial.spl`
- `test/01_unit/app/office/sheets/math_bridge_*_spec.spl` — wrapper specs
