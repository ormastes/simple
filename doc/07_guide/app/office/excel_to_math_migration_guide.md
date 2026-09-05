# Excel-to-Math Library Migration Guide (finalized)

Finalized in-tree form of the `migration_checklist.md` deliverable named by
`doc/03_plan/app/office/excel_to_math_synthesis.md`. That plan scoped **21
prioritized functions**; its own matrix tables list 15 (Phase 2, trigonometry
and basic math) plus 7 (Phase 3, statistics and aggregates) = 22 rows. The
tables below use the plan's numbering and leave the extra row unnumbered rather
than inventing a reconciliation.

Source plans:
- `doc/03_plan/app/office/excel_to_math_lib_migration.md`
- `doc/03_plan/app/office/excel_to_math_synthesis.md`

User-facing companion: `doc/07_guide/app/office/excel_formulas.md`

## What migrated

The rule: numerics move to `std.common.math`, Excel semantics stay in
`src/app/office/sheets/`. `math_bridge.spl` is the seam — a pure
`f64`-in/`f64`-out adapter layer. Domain validation (`#ERR` on `LN(0)`,
`SQRT(-1)`, `ASIN(2)`) stays at the `formula.spl` dispatch site.

### Phase 2 — trigonometry and basic math (15 of 15 wrappers)

| # | Excel | Bridge wrapper | stdlib target |
|---|---|---|---|
| 1 | `SIN` | `excel_sin` | `math_sin` |
| 2 | `COS` | `excel_cos` | `math_cos` |
| 3 | `TAN` | `excel_tan` | `math_sin` / `math_cos` |
| 4 | `ASIN` | `excel_asin` | `math_asin` |
| 5 | `ACOS` | `excel_acos` | `math_acos` |
| 6 | `ATAN` | `excel_atan` | `math_atan` |
| 7 | `SINH` | `excel_sinh` | `math_exp` |
| 8 | `COSH` | `excel_cosh` | `math_exp` |
| 9 | `TANH` | `excel_tanh` | `math_exp` |
| 10 | `LOG` | `excel_log` | `ln_f64` |
| 11 | `LN` | `excel_ln` | `ln_f64` |
| 12 | `LOG10` | `excel_log10` | `ln_f64` |
| 13 | `EXP` | `excel_exp` | `math_exp` |
| 14 | `SQRT` | `excel_sqrt` | `math_sqrt` |
| 15 | `SQRTPI` | `excel_sqrt_pi` | `math_sqrt` + `MATH_PI` |

All 15 are routed from `formula.spl`'s dispatcher. `SQRT` and `SQRTPI` were the
last two; they previously used the file-local Newton's-method `_sqrt_f64` and a
file-local `_PI`.

`DEGREES` and `RADIANS` were routed at the same time (`excel_degrees`,
`excel_radians`) because they were the remaining `_PI` consumers.

### Phase 3 — statistics and aggregates (7 of 7 wrappers)

| # | Excel | Bridge wrapper | Notes |
|---|---|---|---|
| 16 | `SUM` | `excel_sum` | fold |
| 17 | `AVERAGE` | `excel_average` | `mean` from `statistics.spl` |
| 18 | `COUNT` | `excel_count` | returns `i64` |
| 19 | `MIN` | `excel_min` | fold; empty ⇒ `0.0` |
| 20 | `MAX` | `excel_max` | fold; empty ⇒ `0.0` |
| 21 | `PRODUCT` | `excel_product` | fold; empty ⇒ `1.0` |
| — | `SUMSQ` | `excel_sumsq` | fold of squares |

**Status:** the wrappers exist and are specified, but `formula.spl`'s dispatch
for these seven still calls its own `eval_sum` / `eval_average` / `eval_count` /
`eval_min` / `eval_max` / `eval_product` helpers and an inline `SUMSQ` loop. The
empty-range semantics differ between the two sets (`eval_product([])` returns
`0.0`, `excel_product([])` returns `1.0`; `eval_count` returns `f64`,
`excel_count` returns `i64`), so the dispatch reroute is a behaviour change that
must be verified against the formula specs before it lands. It has not been.

## Duplicated implementations removed from `formula.spl`

| Removed | Replaced by |
|---|---|
| `fn _sin_f64` (range reduction + 10-term Taylor series) | `excel_sin` → `math_sin` |
| `fn _cos_f64` (`_sin_f64(x + π/2)`) | `excel_cos` → `math_cos` |
| `fn _atan_f64` (40-term Euler series) | `excel_atan` → `math_atan` |
| `fn _sqrt_f64` (40-iteration Newton's method) | `excel_sqrt` → `math_sqrt` |
| `val _PI` | `MATH_PI` from `std.common.math.math` |

These were the schoolbook approximations. Replacing them with libm-backed SFFI
calls is a precision improvement as well as a de-duplication: the old
`_sin_f64` lost accuracy for large arguments, and `_atan_f64` was a fixed
40-term truncation.

`_atan2_f64`, `_sinh_f64` and `_cosh_f64` remain in `formula.spl` (used by the
complex-number `IM*` functions) but now build on `excel_atan` / `MATH_PI` and
`exp_f64` rather than on the deleted private helpers.

Line-count effect: `formula.spl` went from 9,606 to 9,558 lines. The plans'
"~500-1000 lines" estimate was based on a duplication inventory that had
already been largely worked off by earlier phases; the remaining duplicated
numeric code was 48 lines.

## Verification

Acceptance oracles:
- `test/03_system/plan_acceptance/excel_to_math_lib_migration_spec.spl`
- `test/03_system/plan_acceptance/excel_to_math_synthesis_spec.spl`

Unit specs: `test/01_unit/app/office/sheets/math_bridge_*_spec.spl` (9 files),
`formula_trig_spec.spl`, `formula_math_spec.spl`.

```bash
bin/simple test test/03_system/plan_acceptance/excel_to_math_lib_migration_spec.spl
bin/simple test test/03_system/plan_acceptance/excel_to_math_synthesis_spec.spl
bin/simple test test/01_unit/app/office/sheets/
```

**Known blocker (2026-09-05, macOS aarch64 host):** none of these can be
executed here. Every binary in `bin/release/*/` predates the `unsafe(...)`
capability-block construct that SFFI v2 source-boundary hardening (#75)
introduced into `src/lib/common/math/math.spl`, so any module importing
`std.common.math.math` — which includes `math_bridge.spl` and therefore
`formula.spl` — fails to load with
`parse: in ".../math/math.spl": Unexpected token: expected expression, found
Colon`. Both the inline (`unsafe(capabilities: [ffi]): expr`) and block forms
reproduce on a two-line fixture. Re-run the commands above after a seed
rebuild.
