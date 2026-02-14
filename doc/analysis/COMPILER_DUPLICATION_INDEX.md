# Compiler Duplication Analysis - Complete Index

**Date:** 2026-02-14
**Scope:** src/compiler/ directory (420 files, 136,623 lines)
**Status:** ✅ Comprehensive scan completed

---

## 📋 Quick Navigation

### 🎯 Start Here
- **Quick Reference:** `compiler_duplicates_quick_ref.md` (5 min read)
  - Prioritized list of fixes
  - Risk/time estimates
  - Key statistics

- **Full Analysis:** `phase2_compiler_duplicates.md` (20 min read)
  - Detailed findings per batch
  - Code examples
  - Architectural recommendations

---

## 📊 Key Findings Summary

### Overall Statistics
- **Total files:** 420
- **Total lines:** 136,623
- **Identified duplication:** 7,500-8,000 lines (5.6-6.5%)
- **Phase files:** 26 files with 12,291 lines

### Duplication by Category
1. **Phase-based type duplications** - 3,500-4,000 lines (**HIGH IMPACT**)
2. **Architecture-specific code** - 2,000+ lines (**MEDIUM IMPACT**)
3. **Scattered utilities** - 1,500+ lines (**MEDIUM IMPACT**)
4. **Transformation patterns** - 1,000+ lines (**MEDIUM IMPACT**)

---

## 🎯 Priority Action Items

### 🟢 P0: Green Light (Zero Risk, Start Immediately)

**ISel Helper Duplication**
- Files: `src/compiler/backend/native/isel_{x86_64,aarch64,riscv64}.spl`
- Duplication: 6 functions repeated 3 times
- Lines to save: 60-80
- Time: 1-2 hours
- Risk: **ZERO** - Pure extraction
- Action: Extract to `backend/native/isel_common.spl`

**Encoder Wrapper Duplication**
- Files: `src/compiler/backend/native/encode_{x86_64,aarch64,riscv64}.spl`
- Duplication: 3 functions repeated 3 times
- Lines to save: 200-300
- Time: 1-2 hours
- Risk: **ZERO** - Pure extraction
- Action: Extract to `backend/native/encode_common.spl`

### 🟡 P1: Yellow Light (Low Risk, Next Sprint)

**Error Utility Consolidation**
- Location: 60 files with error handling
- Duplication: 50-100 lines of similar error creation
- Lines to save: 50-100
- Time: 2-3 hours
- Risk: **LOW**
- Action: Create `compiler/error_utils.spl`

### 🟠 P2: Orange Light (Medium Risk, After P1)

**MirVisitor Trait**
- Files: `src/compiler/mir_opt/*.spl` (9 optimization passes)
- Duplication: 200-300 lines of visitor patterns
- Lines to save: 200-300
- Time: 5-8 hours
- Risk: **LOW-MEDIUM**
- Action: Create `compiler/mir_visitor_trait.spl`

**Backend Interface Abstraction**
- Duplication: 300-500 lines
- Lines to save: 300-500
- Time: 6-8 hours
- Risk: **MEDIUM**
- Action: Create trait-based backend layer

### 🔴 P3: Red Light (High Effort, Long-Term)

**Phase Type Consolidation**
- Duplication: 3,500-4,000 lines across 26 phase files
- Lines to save: 3,500-4,000
- Time: 2 weeks
- Risk: **HIGH** - Requires architectural redesign
- Action: Create shared type core, phases extend rather than duplicate

**Type Registry System**
- Duplication: 500-1,000 lines
- Affected: 14 types defined 3-7 times
- Lines to save: 500-1,000
- Time: 1 week
- Risk: **HIGH**
- Action: Centralized type registry

---

## 📁 Document Organization

### Main Analysis Documents

1. **`phase2_compiler_duplicates.md`** (559 lines)
   - Comprehensive analysis of src/compiler/ directory
   - Detailed findings by batch (backend, type system, remaining passes)
   - Code examples of found duplications
   - Refactoring roadmap with phases
   - Recommendations and risk assessment

2. **`compiler_duplicates_quick_ref.md`** (173 lines)
   - Quick statistics and findings
   - Priority ranking (GREEN/YELLOW/RED)
   - Time/savings/risk table
   - Key files to refactor

### Previous Phase 1 Analysis (src/app/ and src/std/)
- `phase1_summary.md` - Executive summary of Phase 1 findings
- `phase1_app_duplicates.md` - App directory analysis
- `phase1_stdlib_utils_duplicates.md` - Standard library utilities
- `DUPLICATION_QUICK_REFERENCE.md` - Phase 1 quick reference

---

## 🔍 Detailed Batch Breakdown

### BATCH 1: Backend (67 files, 25,034 lines)

**Critical Issues:**
- 6 ISel helper functions defined identically in x86_64, aarch64, riscv64
- 3 encoder wrapper functions duplicated across 3 encoders
- Symbol management scattered across backends

**Files of Note:**
- `backend/native/isel_x86_64.spl` (856 lines) - Primary ISel
- `backend/native/isel_aarch64.spl` (777 lines) - aarch64 ISel
- `backend/native/isel_riscv64.spl` (771 lines) - riscv64 ISel
- `backend/native/encode_x86_64.spl` (705 lines)
- `backend/native/encode_aarch64.spl` (540 lines)
- `backend/native/encode_riscv64.spl` (553 lines)

**Duplication Impact:** 60-80 lines of identical utility code

---

### BATCH 2: Type System & HIR/MIR (100 files, ~68,500 lines)

**Critical Issues:**
- 7 definitions of TraitRef (associated_types_phase4*, trait_impl, trait_method_resolution, trait_solver)
- 5 definitions of HirExpr (bidir_phase1*, hir_definitions)
- 5 definitions of EffectEnv (effects* modules)
- 4 definitions each of 6+ other core types

**Major Phase Families:**
1. **associated_types_phase4*** (1,981 lines, 4-way)
   - 47% overlap between phase4a and phase4b
   - All define TraitRef identically

2. **bidir_phase1*** (1,860 lines, 4-way)
   - All define HirExpr
   - Sequential bidirectional type checking phases

3. **higher_rank_poly_phase5*** (2,041 lines, 4-way)
   - Forall type handling
   - Quantifier context management

4. **effects* modules** (1,569 lines, 5-way)
   - Scanner, solver, promises, environment
   - All duplicate EffectEnv

5. **variance_phase6*** (~1,300 lines, 4-way)
   - Variance checking phases

6. **simd_phase9*** (~1,900 lines, 3-way)
   - SIMD optimization phases

**Duplication Impact:** 3,500-4,000 lines due to phase architecture

---

### BATCH 3: Remaining Passes (253 files, ~43,000 lines)

**Major Subsystems:**

1. **Monomorphization (14 files, 6,716 lines)**
   - Well-organized modular system
   - Single large file: deferred.spl (1,405 lines)

2. **MIR Optimization (9 files, 5,344 lines)**
   - auto_vectorize.spl (1,528 lines)
   - loop_opt.spl (957 lines)
   - inline.spl, const_fold.spl, dce.spl, etc.
   - Estimated 1,000+ lines of visitor pattern duplication

3. **Type Inference (5 files, 2,042 lines)**
   - Centralized in inference.spl (1,437 lines)
   - Better organized than backend

---

## 💡 Key Patterns Identified

### Pattern 1: Phase-Based Type Duplication
**Root Cause:** Phase architecture assumes each phase is independent, redefining types
**Example:** TraitRef appears in 7 different files
**Solution:** Shared type core module, phases extend rather than duplicate

### Pattern 2: Architecture-Specific Utilities
**Root Cause:** ISA backends (x86_64, aarch64, riscv64) define identical helper functions
**Example:** isel_alloc_vreg identical in all 3 backends
**Solution:** Extract to shared isel_common.spl

### Pattern 3: Scattered Error Handling
**Root Cause:** Each module implements similar error creation and reporting
**Example:** type_error(), runtime_error(), compile_error() repeated
**Solution:** Centralize in error_utils.spl

### Pattern 4: Visitor Pattern Duplication
**Root Cause:** Each MIR optimization pass implements MIR traversal independently
**Example:** 9 optimization files likely reimplementing visitor 4-5 times
**Solution:** Create MirVisitor trait abstraction

---

## 📈 Refactoring ROI Analysis

### Green (P0) - Maximum ROI
| Task | Time | Savings | Risk | ROI |
|------|------|---------|------|-----|
| ISel helpers | 2h | 60-80 lines | ZERO | 30-40 lines/hr |
| Encoder wrappers | 2h | 200-300 lines | ZERO | 100-150 lines/hr |

### Medium (P1-P2) - Good ROI
| Task | Time | Savings | Risk | ROI |
|------|------|---------|------|-----|
| Error utils | 3h | 50-100 lines | LOW | 16-33 lines/hr |
| MirVisitor | 8h | 200-300 lines | LOW | 25-37 lines/hr |
| Backend abstraction | 8h | 300-500 lines | MED | 37-62 lines/hr |

### Red (P3) - High Effort, High Reward (Long-term)
| Task | Time | Savings | Risk | ROI |
|------|------|---------|------|-----|
| Phase type core | 80h | 3,500-4,000 lines | HIGH | 43-50 lines/hr |
| Type registry | 40h | 500-1,000 lines | HIGH | 12-25 lines/hr |

---

## 🎓 Recommendations

### Immediate (This Week)
1. Extract ISel helpers - **2 hours**, zero risk
2. Extract encoder wrappers - **2 hours**, zero risk
3. Code review and merge

### Short-term (Next Sprint)
1. Create error_utils.spl - **3 hours**
2. Implement MirVisitor trait - **8 hours**
3. Testing and validation

### Medium-term (Next 2-3 Weeks)
1. Backend trait abstraction - **8 hours**
2. Monomorphization cleanup - **6 hours**
3. Type system consolidation planning

### Long-term (After architecture is stable)
1. Phase type consolidation - **2 weeks**
2. Type registry implementation - **1 week**
3. Integration testing

---

## 📞 Questions & Answers

**Q: Why are types defined multiple times?**
A: The compiler uses a phase-based architecture where each phase was developed independently, redefining types rather than sharing them. This was expedient for initial development but creates maintenance burden.

**Q: Can we fix the phase duplication quickly?**
A: No - it requires careful architectural changes to ensure phases work correctly with shared types. Recommended approach: start with easy wins (ISel/encoder), validate refactoring approach, then tackle phases.

**Q: What's the risk of consolidating types?**
A: Each phase may have slightly different requirements. Consolidation requires ensuring all phases work correctly with the unified type definitions. Medium-high risk but manageable with thorough testing.

**Q: Should we do a big refactor or incremental?**
A: **Incremental recommended**: Green items first (zero risk), validate process, then proceed to yellow/orange items. Red items (phases) should wait until green/yellow are done and duplication benefits are proven.

---

## 📚 Related Documents

- Type inference analysis: `type_inference_*.md` (11 files)
- Phase 1 summary: `phase1_summary.md`
- Pattern analysis: `pattern_analysis.txt`

---

## ✅ Checklist for Refactoring

- [ ] Review `compiler_duplicates_quick_ref.md` for overview
- [ ] Review `phase2_compiler_duplicates.md` for details
- [ ] Extract ISel helpers to `backend/native/isel_common.spl`
- [ ] Extract encoder wrappers to `backend/native/encode_common.spl`
- [ ] Create `compiler/error_utils.spl`
- [ ] Run full test suite after each extraction
- [ ] Update architecture documentation
- [ ] Plan Phase 2 refactoring (MirVisitor, type consolidation)

---

**Generated:** 2026-02-14 (Comprehensive Duplication Analysis - Batch 1, 2, and 3)
