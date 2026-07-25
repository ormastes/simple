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

# Add migration verification tests
# Create: test/01_unit/app/office/sheets/formula_math_lib_migration_spec.spl
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

### 4. Remove Duplicated Implementations
Delete unused helper functions:
- `_sin_f64`, `_cos_f64`, `_atan_f64` (now use math lib)
- `_ln_f64`, `_exp_f64`, `_sqrt_f64` (now use special.spl)
- `_PI` constant (now use MATH_PI)

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
- [ ] No performance regression in benchmark suite
- [ ] Excel functions documented as using stdlib math
- [ ] Code size reduced by ~500-1000 lines (duplicated implementations)
- [ ] User-facing guide updated (doc/07_guide/app/office/excel_formulas.md)

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
