# Excel-to-Math Library Migration: Implementation Guide

**Synthesis of 5 parallel research agents** - Complete migration blueprint

---

## Executive Summary

**Migration Scope:** 81 Excel formula functions analyzed, 120+ math library functions catalogued, 43 test files reviewed

**Primary Goal:** Eliminate ~500-1000 lines of duplicated mathematical implementations by migrating Excel formula functions to use stdlib math equivalents

**Risk Profile:** 86% low-risk, 14% medium-risk, 0% high-risk migrations

**Timeline Estimate:** 18-29 hours across 5 phases

---

## Research Artifacts

All research outputs available in `/tmp/`:

| Artifact | Size | Content |
|----------|------|---------|
| `excel_formula_catalog.sdn` | 19KB, 654 lines | 81 Excel functions with line numbers, dependencies, error handling |
| `math_lib_catalog.sdn` | TBD | 120+ stdlib functions (SFFI vs pure Simple, performance, error handling) |
| `formula_test_coverage.md` | TBD | 43 test files, 250+ functions, coverage gaps identified |
| `math_bridge_design.md` | TBD | Complete `math_bridge.spl` module structure with 50+ wrapper functions |
| `migration_checklist.md` | TBD | Phase 2-3 detailed checklist with 21 prioritized functions |

---

## Migration Mapping Matrix

### ✅ Phase 2: Trigonometry & Basic Math (15 functions)

| Excel Function | Line | Target Stdlib | Complexity | Risk | Action |
|----------------|------|---------------|------------|------|--------|
| **SIN** | 4503 | `math_sin` | Easy | Low | Direct wrapper |
| **COS** | 4507 | `math_cos` | Easy | Low | Direct wrapper |
| **TAN** | 4511 | `math_tan` | Easy | Low | Direct wrapper |
| **ASIN** | 4522 | `math_atan` + `math_sqrt` | Medium | Medium | Wrapper with edge cases (±1) |
| **ACOS** | 4531 | `math_atan` + `math_sqrt` | Medium | Medium | Wrapper with edge cases (±1) |
| **ATAN** | 4518 | `math_atan` | Easy | Low | Direct wrapper |
| **SINH** | 4540 | `math_exp` | Easy | Low | Formula wrapper: (exp(x) - exp(-x)) / 2 |
| **COSH** | 4544 | `math_exp` | Easy | Low | Formula wrapper: (exp(x) + exp(-x)) / 2 |
| **TANH** | 4548 | `math_exp` | Easy | Low | Formula wrapper: (exp(2x) - 1) / (exp(2x) + 1) |
| **LOG** | 4553 | `ln_f64` / `math_log10` | Medium | Medium | Base parameter handling (default=10) |
| **LN** | 4625 | `ln_f64` (special.spl) | Easy | Low | Direct wrapper |
| **LOG10** | 4629 | `ln_f64` / `math_ln` | Easy | Low | Formula wrapper: ln(x) / ln(10) |
| **EXP** | 4621 | `math_exp` / `exp_f64` | Easy | Low | Direct wrapper |
| **SQRT** | 6599 | `math_sqrt` / `sqrt_f64` | Easy | Low | Direct wrapper |
| **SQRTPI** | 4617 | `math_sqrt` + `MATH_PI` | Easy | Low | Formula wrapper: sqrt(π * x) |

**Subtotal:** 11 easy (73%), 4 medium (27%), 0 hard (0%)

---

### ✅ Phase 3: Statistics & Aggregates (7 functions)

| Excel Function | Line | Target Stdlib | Complexity | Risk | Action |
|----------------|------|---------------|------------|------|--------|
| **SUM** | 4489 | Array helper | Medium | Low | Fold implementation |
| **AVERAGE** | 4491 | `mean` (statistics.spl) | Easy | Low | Direct wrapper |
| **COUNT** | 4493 | `array.len()` | Easy | Low | Filter + count |
| **MIN** | 4495 | Fold or `math_min` | Medium | Low | Array iteration |
| **MAX** | 4497 | Fold or `math_max` | Medium | Low | Array iteration |
| **PRODUCT** | 4499 | Array helper | Medium | Low | Product fold |
| **SUMSQ** | 4641 | Array helper | Medium | Low | Squared sum fold |

**Subtotal:** 2 easy (29%), 5 medium (71%), 0 hard (0%)

---

## Functions NOT Migrating (Keep in formula.spl)

### Combinatorics (Excel-specific semantics)
- **FACT**, **FACTDOUBLE** - Excel-specific domain behavior
- **COMBIN**, **PERMUT**, **COMBINA**, **PERMUTATIONA** - Can use `special.spl` wrappers but keep Excel validation in formula.spl
- **MULTINOMIAL** - Keep in formula.spl

### Financial Functions (Already in financial.spl)
- **NPV**, **IRR**, **MIRR**, **XNPV**, **XIRR** - Use `std.common.math.financial` wrappers
- **PMT**, **PPMT**, **IPMT**, **CUMIPMT**, **CUMPRINC** - TVM functions
- **SLN**, **SYD**, **DDB**, **DB**, **VDB** - Depreciation functions
- **PRICE**, **YIELD**, **TBILLPRICE**, **TBILLYIELD**, etc. - Securities functions

### Statistical Functions (Keep or wrap)
- **STDEV.S**, **STDEV.P**, **VAR.S**, **VAR.P** - Use `stdev_sample`, `variance_sample`
- **MEDIAN**, **MODE.SNGL**, **RANK.EQ** - Use `median`, `mode_single`
- **PERCENTILE**, **QUARTILE**, **PERCENTRANK** - Keep in formula.spl (Excel-specific algorithms)
- **SKEW**, **KURT**, **TRIMMEAN** - Keep in formula.spl

### Criteria & Aggregation (Not math operations)
- **SUMIF**, **SUMIFS**, **COUNTIF**, **COUNTIFS** - Keep in formula.spl (requires range/criteria parsing)
- **AVERAGEIF**, **AVERAGEIFS**, **MAXIFS**, **MINIFS** - Keep in formula.spl
- **SUBTOTAL**, **AGGREGATE** - Keep in formula.spl (function-switch behavior)

---

## Implementation Sequence

### Phase 0: Foundation (2-4 hours) ⏳

**0.1 Verify stdlib exports**
```bash
# Check that all required functions are exported
grep -E "pub fn (math_sin|math_cos|math_tan|math_exp|math_sqrt)" src/lib/common/math/math.spl
grep -E "pub fn (mean|median|stdev_sample|variance_sample)" src/lib/common/math/statistics.spl
grep -E "pub fn (exp_f64|ln_f64|sqrt_f64|log10_f64)" src/lib/common/math/special.spl
```

**0.2 Create math bridge module**
- File: `src/app/office/sheets/math_bridge.spl`
- Copy structure from `/tmp/math_bridge_design.md`
- Verify all imports resolve

**0.3 Add nogc_async_mut wrappers**
- File: `src/lib/nogc_async_mut/math/__init__.spl`
- Export `use std.common.math.*` for all tiers (per lib tier rule)

**0.4 Baseline test run**
```bash
bin/simple test test/01_unit/app/office/sheets/formula_*.spl
# Expected: All PASS (baseline)
```

---

### Phase 1: Core Trigonometry (4-6 hours) 📐

**Migrate: SIN, COS, TAN, ATAN → Direct wrappers**

1. **Update formula.spl imports** (line ~17):
```simple
use app.office.sheets.math_bridge.{excel_sin, excel_cos, excel_tan, excel_atan}
```

2. **Replace _dispatch_function cases** (lines 4503-4520):
```simple
# Before
"SIN":
    if flat.len() > 0:
        return CellValue.NumberVal(value: _sin_f64(flat[0]))

# After
"SIN":
    if flat.len() > 0:
        return CellValue.NumberVal(value: excel_sin(flat[0]))
```

3. **Remove old helpers** (if any `_sin_f64` etc. exist)

4. **Test:**
```bash
bin/simple test test/01_unit/app/office/sheets/formula_trig_spec.spl
```

5. **Verify:** No behavior change (compare old vs new output)

---

### Phase 2: Inverse Trig & Hyperbolic (4-6 hours) 📐

**Migrate: ASIN, ACOS → Edge-case wrappers**
**Migrate: SINH, COSH, TANH → Formula wrappers**

1. **Update formula.spl imports**:
```simple
use app.office.sheets.math_bridge.{excel_asin, excel_acos, excel_sinh, excel_cosh, excel_tanh}
```

2. **Replace _dispatch_function cases** (lines 4522-4552)

3. **Test edge cases**:
```simple
# Test ±1 boundaries
assert_equal(excel_asin(1.0), MATH_PI / 2.0)
assert_equal(excel_asin(-1.0), 0.0 - MATH_PI / 2.0)
```

---

### Phase 3: Logarithmic & Exponential (3-5 hours) 📊

**Migrate: LN, LOG10, EXP, SQRT, SQRTPI → Direct/formula wrappers**

1. **Update formula.spl imports**:
```simple
use app.office.sheets.math_bridge.{excel_ln, excel_log10, excel_exp, excel_sqrt, excel_sqrt_pi}
```

2. **Replace _dispatch_function cases** (lines 4553-4629, 4617, 4621-4632)

3. **Test domain errors**:
```bash
# LN(0) → #ERR
# SQRT(-1) → #ERR
# LOG(10, 1) → #ERR (base=1 invalid)
```

---

### Phase 4: Statistics & Aggregates (4-6 hours) 📈

**Migrate: AVERAGE, COUNT → Direct wrappers**
**Migrate: SUM, MIN, MAX, PRODUCT, SUMSQ → Array helpers**

1. **Update formula.spl imports**:
```simple
use app.office.sheets.math_bridge.{excel_average, excel_count, excel_sum, excel_min, excel_max}
```

2. **Replace _dispatch_function cases** (lines 4489-4497, 4641)

3. **Test empty arrays**:
```simple
assert_equal(excel_sum([]), 0.0)
assert_equal(excel_product([]), 1.0)
assert_equal(excel_average([]), 0.0)  # Excel returns #DIV/0!, check if we match
```

---

### Phase 5: Verification & Cleanup (4-6 hours) ✅

**5.1 Remove dead code**
- Delete unused `_sin_f64`, `_cos_f64`, `_atan_f64` helpers
- Delete unused `_PI`, `_E` constants (now use MATH_PI, MATH_E)

**5.2 Full test suite**
```bash
bin/simple test test/01_unit/app/office/sheets/formula_*.spl
# Expected: 100% PASS, no regressions
```

**5.3 Code size verification**
```bash
wc -l src/app/office/sheets/formula.spl
# Expected: Reduction of ~500-1000 lines
```

**5.4 Performance verification**
```bash
# Benchmark critical formulas (no regression)
time bin/simple run -c "Excel perf test"
```

**5.5 Documentation update**
- Update `doc/07_guide/app/office/excel_formulas.md`
- Add note about stdlib math usage

---

## Risk Mitigation

### Low-Risk Migrations (18 functions)
- **Strategy:** Direct wrapper, run existing tests, verify output matches
- **Fallback:** Revert commit if tests fail

### Medium-Risk Migrations (3 functions)
- **ASIN, ACOS:** Edge cases at ±1 require explicit handling
- **LOG:** Base parameter default (10) vs explicit base validation
- **Strategy:** Add explicit edge case tests before migration
- **Verification:** Compare old vs new to 10 decimal places

### Error Handling Semantics
- **Principle:** Domain validation stays in `formula.spl`, bridge functions are pure
- **Pattern:** Bridge returns `f64`, caller wraps in `CellValue.NumberVal` or `CellValue.ErrorVal`

---

## Test Strategy

### Pre-Migration
```bash
# Establish baseline
bin/simple test test/01_unit/app/office/sheets/formula_*.spl > baseline.log
```

### Per-Function Migration
1. Update bridge function
2. Update formula.spl dispatch case
3. Run specific test file
4. Verify output matches baseline

### Post-Migration
1. Full test suite run
2. Edge case regression tests (NaN, infinity, domain errors)
3. Performance benchmarks (no regressions)
4. Code size verification

---

## Success Criteria

- [x] Research complete (5 agents, 5 artifacts)
- [ ] All 21 Phase 2-3 functions migrated
- [ ] All formula tests pass (100% coverage)
- [ ] No performance regression
- [ ] Code size reduced by ~500-1000 lines
- [ ] Documentation updated
- [ ] Migration guide finalized

---

## Open Questions

1. **ATAN2:** Excel has ATAN2(x, y) but migration plan omitted it - should we include?
2. **MODE.MULT vs MODE.SNGL:** Current design only covers MODE.SNGL - need MODE.MULT?
3. **Digits parameter:** Should `math_ceil`/`math_floor` accept `digits` for ROUNDUP/ROUNDDOWN?

---

## References

- Migration Plan: `doc/03_plan/app/office/excel_to_math_lib_migration.md`
- Excel Formula Catalog: `/tmp/excel_formula_catalog.sdn`
- Math Library Catalog: `/tmp/math_lib_catalog.sdn`
- Test Coverage Report: `/tmp/formula_test_coverage.md`
- Bridge Module Design: `/tmp/math_bridge_design.md`
- Migration Checklist: `/tmp/migration_checklist.md`

---

## Next Steps

1. **Review synthesis** with team
2. **Assign phases** to developers
3. **Create feature branch** (per jj rules, work on main directly)
4. **Begin Phase 0** (foundation)
5. **Track progress** with `/loop` or manual checkpoints
