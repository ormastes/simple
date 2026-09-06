# Excel Function to Math Library Migration Plan

## Problem Statement

**Current State:** Excel formula functions in `src/app/office/sheets/formula.spl` duplicate mathematical implementations that already exist in `src/lib/common/math/`.

**Impact:**
- Code duplication maintenance burden
- Inconsistent behavior between Excel formulas and stdlib math
- Harder for users to transition from Excel macros to Simple scripts
- Mathematical constants scattered (_PI vs MATH_PI)

## Duplication Analysis

### Excel Formula Functions (formula.spl)
```simple
# Trigonometry (using _sin_f64, _cos_f64, _atan_f64, _sqrt_f64, _exp_f64)
SIN, COS, TAN, ASIN, ACOS, ATAN
SINH, COSH, TANH

# Logarithmic & Exponential (using _ln_f64, _exp_f64)
LOG, LN, LOG10, EXP

# Power & Roots (using _pow_f64, _sqrt_f64)
SQRT, SQRTPI, POWER

# Rounding (using _ceil_f64, _floor_f64)
ROUNDUP, ROUNDDOWN, EVEN, ODD, MROUND

# Array Aggregates (custom implementations)
SUM, AVERAGE, COUNT, MIN, MAX, PRODUCT, SUMSQ

# Combinatorics (using _fact_i64)
COMBIN, PERMUT, COMBINA, PERMUTATIONA, FACT, FACTDOUBLE

# Statistics
QUOTIENT, STDEV, VAR, etc.
```

### Math Library Equivalents (src/lib/common/math/)
```simple
# math.spl
math_sin, math_cos, math_tan, math_pow, math_exp, math_sqrt
math_abs, math_round, math_trunc, math_floor, math_ceil
math_min, math_max, MATH_PI, MATH_E

# statistics.spl  
mean, median, mode, stdev_sample, variance_sample
avedev, devsq, skew, kurtosis

# financial.spl
TVM functions, cashflow, depreciation, daycount, T-bill

# special.spl
exp_f64, ln_f64, sqrt_f64, log10_f64

# distributions.spl
PDF/CDF for beta, binom, chi2, F, gamma, hypergeom, norm, poisson, Student's t
```

## Migration Strategy

### Phase 1: Foundation (Low Risk)
1. **Add public exports** to `src/lib/common/math/__init__.spl`:
   - Export `math.*`, `statistics.*`, `financial.*`, `special.*`
   - Ensure `nogc_async_mut` wrappers exist (per lib tier rule)

2. **Create excel-to-math bridge** in `src/app/office/sheets/math_bridge.spl`:
   ```simple
   use std.common.math.{math_sin, math_cos, math_tan, 
                        math_exp, math_ln, math_log10,
                        math_sqrt, math_pow, math_abs,
                        math_floor, math_ceil, math_round,
                        math_min, math_max, MATH_PI, MATH_E}
   use std.common.math.statistics.{mean, median, stdev_sample, variance_sample}
   use std.common.math.special.{exp_f64, ln_f64, sqrt_f64}
   ```

### Phase 2: Trigonometry & Basic Math (Medium Risk)
Replace implementations in `formula.spl` _dispatch_function:

```simple
# Before (custom impl)
"SIN":
    if flat.len() > 0:
        return CellValue.NumberVal(value: _sin_f64(flat[0]))

# After (math lib)
"SIN":
    if flat.len() > 0:
        return CellValue.NumberVal(value: math_sin(flat[0]))
```

**Functions to migrate:**
- SIN → math_sin
- COS → math_cos  
- TAN → math_tan
- ASIN → math_asin (needs wrapper: asin(x) = atan(x / sqrt(1 - x²)))
- ACOS → math_acos (needs wrapper: acos(x) = π/2 - atan(x / sqrt(1 - x²)))
- ATAN → math_atan
- SINH → (exp(x) - exp(-x)) / 2 → math_sinh if available, else wrapper
- COSH → (exp(x) + exp(-x)) / 2 → math_cosh if available, else wrapper
- TANH → (exp(2x) - 1) / (exp(2x) + 1) → math_tanh if available, else wrapper
- LOG → math_log10 or wrapper using ln_f64
- LN → ln_f64
- LOG10 → ln_f64(x) / ln_f64(10)
- EXP → math_exp or exp_f64
- SQRT → math_sqrt or sqrt_f64
- SQRTPI → sqrt(π * x) → wrapper

### Phase 3: Statistics & Aggregates (Medium Risk)
```simple
# Migrate array operations
"SUM":
    return CellValue.NumberVal(value: sum(flat))  # Use stdlib sum if exists
    
"AVERAGE":
    return CellValue.NumberVal(value: mean(flat))
    
"MIN":
    return CellValue.NumberVal(value: fold_min(flat))
    
"MAX":
    return CellValue.NumberVal(value: fold_max(flat))
```

**Functions to migrate:**
- SUM → array sum helper or stdlib function
- AVERAGE → mean()
- COUNT → array.len()
- MIN → fold_min() or math_min applied pairwise
- MAX → fold_max() or math_max applied pairwise
- PRODUCT → array product helper
- SUMSQ → squared sum helper

### Phase 4: Combinatorics (Low Risk)
- FACT, FACTDOUBLE → Keep in formula.spl (Excel-specific semantics)
- COMBIN, PERMUT, COMBINA, PERMUTATIONA → Keep or extract to combinatorics module

### Phase 5: Financial (Low Risk)
- Many TVM functions already in `financial.spl`
- NPV, IRR, PV, FV, PMT → migrate to std.common.math.financial wrappers

## Implementation Steps

### 1. Create Migration Test Coverage
```bash
# Ensure all existing formula tests pass
bin/simple test test/01_unit/app/office/sheets/formula_*.spl

# Migration verification tests (shipped as the math_bridge_*_spec.spl family, 9 files,
# not the single formula_math_lib_migration_spec.spl planned here):
# test/01_unit/app/office/sheets/math_bridge_spec.spl, math_bridge_stats_spec.spl, ...
```

### 2. Add Math Bridge Module
```simple
# src/app/office/sheets/math_bridge.spl
use std.common.math.math.{math_sin, math_cos, math_tan, math_pow, math_exp,
                           math_sqrt, math_abs, math_floor, math_ceil, math_round,
                           math_min, math_max, MATH_PI, MATH_E}
use std.common.math.statistics.{mean, median, stdev_sample, variance_sample}
use std.common.math.special.{exp_f64, ln_f64, sqrt_f64}

# Excel-compatible wrappers with error handling
fn excel_sin(x: f64) -> f64:
    math_sin(x)

fn excel_asin(x: f64) -> f64:
    if x == 1.0:
        return MATH_PI / 2.0
    if x == -1.0:
        return 0.0 - MATH_PI / 2.0
    math_atan(x / math_sqrt(1.0 - x * x))

fn excel_acos(x: f64) -> f64:
    if x == 1.0:
        return 0.0
    if x == -1.0:
        return MATH_PI
    MATH_PI / 2.0 - math_atan(x / math_sqrt(1.0 - x * x))
```

### 3. Update formula.spl _dispatch_function
Replace internal `_sin_f64` calls with `math_bridge::excel_sin` etc.

#### Empty-range decision for the aggregate reroute (2026-09-05) — DECIDED, NOT YET APPLIED

The remaining `_dispatch_function` aggregates (`"COUNT"` -> `eval_count`,
`"PRODUCT"` -> `eval_product`, `formula.spl:4203,4209`) are the only twins whose
observable behaviour DIFFERS from the bridge, so they cannot be rerouted blind:

| empty input | `eval_*` (spreadsheet twin)   | `excel_*` (library twin)      |
|-------------|------------------------------|-------------------------------|
| PRODUCT     | `0.0` (`formula.spl:8451`)   | `1.0` (`math_bridge.spl:136`) |
| COUNT       | `0.0`, returns `f64`         | `0`, returns `i64`            |

**Decision: reroute through the bridge, but keep the spreadsheet semantics at
the dispatch boundary** — a `flat.len() == 0` guard returning `0.0` for
`"PRODUCT"` before calling `excel_product`, and `excel_count(flat).to_f64()`
for `"COUNT"`.

Rationale: the two answers are not a disagreement to be resolved, they are two
correct answers to two different questions, and BOTH are pinned by live specs.
`excel_product([]) == 1.0` (the multiplicative identity) is asserted four times
— `math_bridge_spec.spl:102`, `math_bridge_working_spec.spl:148`,
`math_bridge_comprehensive_spec.spl:178,267` — so flipping the library twin
would break them. Excel itself returns 0 for `=PRODUCT()` over an all-blank
range, which is what the spreadsheet surface must keep. Putting the guard at
the dispatch boundary deletes the duplicated bodies (the point of the plan)
while leaving both observable behaviours byte-identical, and `excel_count`'s
`i64` is widened at the same boundary rather than changing the library's return
type.

**Not applied yet, deliberately.** The change cannot be verified: the plan's own
oracle (`<binary> test test/01_unit/app/office/sheets/`) reports `79 total, 0
passed, 79 failed` BEFORE any change, for three infrastructure reasons unrelated
to formulas — see
`doc/08_tracking/bug/test_runner_ulimit_caps_unusable_on_macos_2026-09-05.md`.
Landing a real behaviour change with no working regression gate would be
guessing. Apply it once that suite runs.

### 4. Remove Duplicated Implementations
Delete unused helper functions:
- `_sin_f64`, `_cos_f64`, `_atan_f64` (now use math lib) — **DELETED 2026-09-05.**
  All call sites route through `excel_sin` / `excel_cos` / `excel_atan`.
- `_sqrt_f64` (now use special.spl) — **DELETED 2026-09-05**; the `"SQRT"` case now
  calls `excel_sqrt`. `_ln_f64` / `_exp_f64` no longer exist (removed earlier).
- `_PI` constant (now use MATH_PI) — **DELETED 2026-09-05**; `formula.spl` imports
  `MATH_PI` from `std.common.math.math`, and `"SQRTPI"` / `"DEGREES"` / `"RADIANS"`
  now call `excel_sqrt_pi` / `excel_degrees` / `excel_radians`.

`_atan2_f64`, `_sinh_f64` and `_cosh_f64` deliberately remain (used by the complex
`IM*` functions) but now build on `excel_atan` / `MATH_PI` / `exp_f64`.
`formula.spl`: 9,606 -> 9,558 lines.

### 5. Update SPipe Tests
- Ensure all formula specs pass after migration
- Add regression tests for edge cases (NaN, infinity, domain errors)

## Benefits

1. **Reduced Duplication**: Single source of truth for math operations
2. **Better Performance**: Math lib uses optimized SFFI calls
3. **Consistency**: Excel macros and Simple scripts use same implementations
4. **Easier Migration**: Users familiar with Excel can leverage stdlib math functions
5. **Maintainability**: Bug fixes in math lib automatically improve Excel formulas

## Risks & Mitigation

| Risk | Impact | Mitigation |
|------|--------|------------|
| Behavior change in edge cases | High | Comprehensive test coverage; parallel run comparing old vs new |
| Performance regression | Medium | Benchmark critical formulas; optimize if needed |
| Breaking existing user macros | High | Maintain exact Excel semantics in wrappers |

## Success Criteria

- [ ] All formula tests pass (100% coverage)
  - blocked 2026-09-05, three stacked infrastructure blockers, none of them a
    formula defect: (1) `ulimit -v` is unimplemented on Darwin so every bounded
    child exited 125 (FIXED in `src/lib/nogc_sync_mut/io/resource_scope.spl`);
    (2) the runner's `ulimit -u 64` is a per-UID cap that makes `timeout` fail
    to fork on a workstation; (3) DOMINANT -- the deny-level
    `spipe_empty_examples` lint does not recognise `assert_*` as a real
    assertion, so `simple test`'s compile-first path fails all 79 sheets specs
    that every one of which PASSES under `simple run`. Full evidence and fix
    order: doc/08_tracking/bug/test_runner_ulimit_caps_unusable_on_macos_2026-09-05.md
- [ ] No performance regression in benchmark suite
- [ ] Excel functions documented as using stdlib math
- [ ] Code size reduced by ~500-1000 lines (duplicated implementations)
- [ ] User-facing guide updated (doc/07_guide/app/office/excel_formulas.md)
  - status 2026-09-05: the guide now EXISTS and documents the
    formula -> `math_bridge` -> `std.common.math` chain, the full function map and
    the ASIN/ACOS endpoint values. Box left OPEN only because its `it` cannot be
    executed on this host — see the blocker note below.

**Blocker: no acceptance `it` is executable on this host (2026-09-05).** Every
deployed binary predates the `unsafe(...)` capability blocks that
`1b4edca296c` (SFFI v2 hardening, #75) added to `src/lib/common/math/math.spl`,
so any module importing `std.common.math.math` — including `math_bridge.spl`
and therefore `formula.spl` — fails to load
(`parse: ... Unexpected token: expected expression, found Colon`). No box is
ticked, per the tick-only-on-a-passing-`it` rule. Re-run after a seed redeploy:
`doc/08_tracking/bug/stale_deployed_binaries_reject_current_language_sspec_scorer_unrunnable_2026-09-05.md`
(section "Second instance, same class").

## Timeline Estimate

- Phase 1 (Foundation): 2-4 hours
- Phase 2 (Trig/Basic Math): 4-6 hours
- Phase 3 (Statistics): 4-6 hours
- Phase 4 (Combinatorics): 2-3 hours
- Phase 5 (Financial): 2-4 hours
- Testing & Verification: 4-6 hours

**Total**: 18-29 hours

## Open Questions

1. Should we create a dedicated `stdlib.common.math.excel` module for Excel-compatible wrappers?
2. What to do with functions that have no stdlib equivalent (FACTDOUBLE, BAHTTEXT)?
3. Should array operations (SUM, AVERAGE) migrate to stdlib or stay Excel-specific?

## References

- Excel functions: `src/app/office/sheets/formula.spl`
- Math library: `src/lib/common/math/`
- Test specs: `test/01_unit/app/office/sheets/formula_*.spl`
- Statistics functions: `src/lib/common/math/statistics.spl`
- Financial functions: `src/lib/common/math/financial.spl`
- Bridge module (shipped): `src/app/office/sheets/math_bridge.spl` (`excel_sin` .. `excel_ceiling`),
  imported by `formula.spl:19`

## Acceptance

Runnable oracles for the remaining open boxes: `test/03_system/plan_acceptance/excel_to_math_lib_migration_spec.spl`
(tagged `@tag:in-development`; one `it` per open box — see
`doc/03_plan/agent_tasks/plan_remains_acceptance_2026-09-05.md`).
