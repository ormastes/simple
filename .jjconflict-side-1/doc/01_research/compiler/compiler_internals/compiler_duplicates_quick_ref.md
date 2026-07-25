# Compiler Duplication Analysis - Quick Reference

**Comprehensive scan of src/compiler/ directory (420 files, 136,623 lines)**

---

## Quick Stats

- **Total duplication:** 7,500-8,000 lines (5.6-6.5% of compiler code)
- **Phase files:** 26 files with 12,291 lines (9% duplication within phases)
- **Backend duplication:** 25,034 lines with 60-80 identical ISel lines
- **Type system duplication:** 14 types defined 3-7 times each

---

## BATCH 1: Backend (67 files, 25,034 lines)

### ✅ EASY FIX: ISel Helper Duplication
- **6 functions duplicated 3 times each** (x86_64, aarch64, riscv64)
  - `isel_alloc_vreg`, `isel_get_vreg`, `isel_frame_offset`, `isel_alloc_frame_slot`
  - `isel_last_string_label`, `isel_add_string_data`, `isel_add_extern`
- **Lines:** 60-80 identical code
- **Fix:** Extract to `backend/native/isel_common.spl`
- **Risk:** Zero
- **Time:** 1-2 hours

### ✅ EASY FIX: Encoder Wrapper Duplication
- **3 functions duplicated 3 times each**
  - `encode_module()`, `encode_function()`, `encode_inst()`
- **Files:** `encode_x86_64.spl`, `encode_aarch64.spl`, `encode_riscv64.spl`
- **Fix:** Extract to `backend/native/encode_common.spl`
- **Risk:** Zero
- **Time:** 1-2 hours

### 🔶 MEDIUM: Backend Error Handling
- Error creation patterns duplicated across backends
- Solutions: Centralize in `error_utils.spl`

---

## BATCH 2: Type System & HIR/MIR (100 files, 68,500 lines)

### 🔴 HARD: Phase-Based Type Duplication (3,500-4,000 lines)

#### associated_types_phase4* (4-way, 1,981 lines)
```
phase4a: 398 lines
phase4b: 530 lines (47% shared with phase4a)
phase4c: 488 lines
phase4d: 565 lines
────────────────
Total: 1,981 lines
Shared type: TraitRef (×4 + 3 other modules = 7 total)
```

#### bidir_phase1* (4-way, 1,860 lines)
```
phase1a: 526 lines
phase1b: 393 lines
phase1c: 416 lines
phase1d: 525 lines
────────────────
Total: 1,860 lines
Shared type: HirExpr (×4 + hir_definitions = 5 total)
```

#### higher_rank_poly_phase5* (4-way, 2,041 lines)
```
phase5a: 437 lines
phase5b: 433 lines
phase5c: 596 lines
phase5d: 575 lines
────────────────
Total: 2,041 lines
```

### Type Definitions (14 types defined multiple times)

| Type | Count | Files |
|------|-------|-------|
| TraitRef | 7 | associated_types_phase4*, trait_impl, trait_method_resolution, trait_solver |
| HirExpr | 5 | bidir_phase1*, hir_definitions |
| EffectEnv | 5 | effects*, effects_env, effects_promises, effects_scanner, effects_solver |
| ResolvedModule | 4 | resolver/loader modules |
| VarianceOps | 4 | variance_phase6* |
| TypeVar | 4 | type inference modules |
| TypeInferencer | 4 | type inference/checking |
| MacroRegistry | 4 | macro modules |
| MacroDef | 4 | macro definitions |

### 🔶 MEDIUM: Effects System (5-way, 1,569 lines)
```
effects.spl:         439 lines
effects_solver.spl:  399 lines
effects_scanner.spl: 286 lines
effects_promises.spl: 274 lines
effects_env.spl:     171 lines
───────────────────
Total: 1,569 lines
Shared type: EffectEnv (appears in all 5)
```

---

## BATCH 3: Remaining Passes (253 files, 43,000 lines)

### 🔶 MEDIUM: Monomorphization (14 files, 6,716 lines)
- Well-modularized system
- `deferred.spl` is large (1,405 lines)
- InstantiationRecord duplicated 3 times

### 🔶 MEDIUM: MIR Optimization Passes (9 files, 5,344 lines)
```
auto_vectorize.spl: 1,528 lines
loop_opt.spl:       957 lines
inline.spl:         726 lines
const_fold.spl:     456 lines
dce.spl:            423 lines
cse.spl:            370 lines
copy_prop.spl:      346 lines
mod.spl:            326 lines
simd_lowering.spl:  212 lines
──────────────────
Total: 5,344 lines
```
- **Duplication:** Likely 1,000+ lines of shared visitor patterns
- **Fix:** Create `MirVisitor` abstract trait

---

## Priority Ranking

### 🟢 GREEN (Start Now)
1. **ISel helpers** - 60-80 lines, 1-2 hrs, zero risk
2. **Encoder wrappers** - 200-300 lines, 1-2 hrs, zero risk
3. **Error utilities** - 50-100 lines, 2-3 hrs, zero risk

### 🟡 YELLOW (After Green)
1. **MirVisitor trait** - 200-300 lines saved, 5-8 hrs, low risk
2. **Backend error handling** - 100-200 lines, 3-4 hrs, low-medium risk
3. **Monomorphization cleanup** - 100-200 lines, 4-6 hrs, medium risk

### 🔴 RED (Long-term, Architectural)
1. **Phase type consolidation** - 3,500-4,000 lines saved, 2+ weeks, high risk
2. **Type registry system** - 500-1,000 lines saved, 1+ week, high risk
3. **Backend trait abstraction** - 300-500 lines, 1 week, medium-high risk

---

## Estimated Time Investments vs Savings

| Task | Savings | Time | Risk | Priority |
|------|---------|------|------|----------|
| ISel helpers | 60-80 | 2h | Zero | P0 |
| Encoder wrappers | 200-300 | 2h | Zero | P0 |
| Error utilities | 50-100 | 3h | Zero | P1 |
| MirVisitor trait | 200-300 | 8h | Low | P2 |
| Type consolidation | 3,500-4,000 | 2w | High | P3 |
| Type registry | 500-1,000 | 1w | High | P3 |

---

## See Also

Full detailed analysis: **doc/analysis/phase2_compiler_duplicates.md**

Key files to refactor:
- `src/compiler/backend/native/isel_*.spl` (3 files)
- `src/compiler/backend/native/encode_*.spl` (3 files)
- `src/compiler/associated_types_phase4*.spl` (4 files)
- `src/compiler/bidir_phase1*.spl` (4 files)
- `src/compiler/higher_rank_poly_phase5*.spl` (4 files)
- `src/compiler/effects*.spl` (5 files)
