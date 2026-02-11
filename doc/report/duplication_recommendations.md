# Duplication Analysis - Recommendations for Future Work

**Date:** 2026-02-11
**Status:** Analysis Complete

---

## Summary of Current State

### ✅ Completed Work

1. **Phase 3: Documentation** (2026-02-11)
   - Created `src/compiler/README.md` and `src/compiler_core/README.md`
   - Documented ~15K lines of intentional duplication (bootstrap requirement)
   - Updated `DUPLICATION_CLEANUP_COMPLETE.md` with Phase 4 history

2. **Previous Cleanups** (2026-02-10)
   - Removed 318 duplicate test files (core_system, integration_e2e)
   - Test file duplicates already addressed in version control

### ⚠️ Deferred Work

1. **Phase 1: Test Consolidation**
   - Finding: Test files were already cleaned up in previous commits
   - Current state: No duplicate test files in version control

2. **Phase 2: Type Mapper Abstraction**
   - Decision: Skipped due to bootstrap constraints
   - Rationale: Would break compiler/ ↔ compiler_core/ separation

---

## Remaining Duplication Patterns

### 1. Phase Files (~12K lines)

**Location:** `src/compiler/*_phase*.spl` (27 files)

**Examples:**
- `bidir_phase1a.spl` through `bidir_phase1d.spl` (4 files, ~1.8K lines)
- `associated_types_phase4a-d.spl` (4 files, ~2.1K lines)
- `higher_rank_poly_phase5a-d.spl` (4 files, ~2.3K lines)
- `variance_phase6a-d.spl` (4 files, ~1.9K lines)
- `macro_checker_phase7a-c.spl` (3 files, ~1.5K lines)
- `const_keys_phase8a-c.spl` (3 files, ~1.2K lines)
- `simd_phase9a-c.spl` (3 files, ~1.2K lines)

**Pattern:**
Each feature (bidirectional checking, associated types, etc.) is split into phases representing incremental development:
- Phase A: Foundation (enums, types)
- Phase B: Core logic
- Phase C: Integration
- Phase D: Optimization

**Duplication Type:** Development evolution
**Production Impact:** Low (these files are for development tracking)

**Recommendation:**
- **Option 1:** Consolidate each feature into single files (e.g., `bidir_phase1a-d` → `bidirectional_checking.spl`)
- **Option 2:** Move to `doc/design/phases/` as historical reference
- **Option 3:** Keep as-is (documents development process)

**Estimated Impact:** ~8K lines could be consolidated (67% reduction across phase files)

**Risk:** Medium - these files might be referenced by development docs or tests

---

### 2. Validator Pattern (~14 files)

**Location:** Various `*_validator.spl`, `*_checker.spl`, `*_check.spl` files

**Examples:**
- `di_validator.spl` (671 lines)
- `visibility_checker.spl` (600+ lines)
- `safety_checker.spl` (500+ lines)
- `simd_check.spl` (400+ lines)
- `verification_checker.spl` (350+ lines)
- `macro_validation.spl` (300+ lines)

**Pattern:**
Each validator follows similar structure:
1. Define error types
2. Implement `validate_X(context, item)` functions
3. Collect and report errors
4. Integrate with compiler pipeline

**Duplication Type:** Structural similarity (not exact duplication)
**Production Impact:** Medium (used in active compilation)

**Recommendation:**
Extract common validation framework:
```simple
# src/compiler/validation/framework.spl
class ValidationContext:
    errors: [ValidationError]
    warnings: [ValidationWarning]

fn run_validator(ctx: ValidationContext, rules: [ValidationRule]) -> ValidationResult
fn report_errors(ctx: ValidationContext, formatter: ErrorFormatter)
```

**Estimated Impact:** ~2K lines of boilerplate could be extracted

**Risk:** High - validators are core to compiler correctness, refactoring requires extensive testing

---

### 3. Builder Pattern (~8 files)

**Location:** Various `*_builder.spl` files

**Examples:**
- `baremetal/table_builder.spl` (445 lines)
- `blocks/builder.spl` (380 lines)
- `backend/matrix_builder.spl` (350 lines)
- `backend/llvm_ir_builder.spl` (300 lines)
- `incremental_builder.spl` (620 lines)

**Pattern:**
Each builder implements:
1. `new_builder()` - Constructor
2. `builder_add_X()` - Incremental operations
3. `builder_build()` - Finalization
4. Error handling and validation

**Duplication Type:** Design pattern similarity
**Production Impact:** Low to Medium

**Recommendation:**
- **Option 1:** Extract generic builder trait (if Full Simple supports it)
- **Option 2:** Leave as-is (pattern is clear and established)

**Estimated Impact:** ~500 lines of boilerplate

**Risk:** Low - builders are relatively independent

---

### 4. Backend ISA Encoders (High Similarity)

**Location:** `src/compiler/backend/native/`

**Files:**
- `isel_x86_64.spl` (751 lines)
- `isel_aarch64.spl` (777 lines)
- `isel_riscv64.spl` (771 lines)
- `encode_x86_64.spl` (620 lines)
- `encode_aarch64.spl` (580 lines)
- `encode_riscv64.spl` (550 lines)

**Pattern:**
Each ISA has nearly identical structure:
1. Instruction selection rules
2. Register allocation interface
3. Encoding to machine code
4. Relocation handling

**Duplication Type:** Cross-ISA structural similarity
**Production Impact:** High (core code generation)

**Recommendation:**
Create ISA abstraction layer:
```simple
# src/compiler/backend/native/isa_traits.spl
trait ISA:
    fn select_instruction(mir: MirInst) -> [MachInst]
    fn encode_instruction(inst: MachInst) -> [u8]
    fn register_count() -> i64
    fn calling_convention() -> CallingConvention
```

**Estimated Impact:** ~1.5K lines could be unified

**Risk:** Very High - incorrect abstraction could break native code generation for all platforms

---

## Recommended Action Plan

### Immediate Actions (Low Risk)

1. **Document Phase Files** ✅ PRIORITY
   - Add `src/compiler/PHASE_FILES.md` explaining their purpose
   - Mark as development history in comments
   - Update CLAUDE.md to mention phase file patterns

2. **Extract Builder Utilities**
   - Create `src/compiler/utils/builder_helpers.spl`
   - Extract common error formatting
   - Extract common validation patterns
   - Low risk, moderate impact (~500 lines)

### Medium-Term Actions (Medium Risk)

3. **Consolidate Phase Files**
   - Merge phase files into single feature files
   - Move to `doc/design/phases/` if historical value needed
   - High impact (~8K lines), medium risk

4. **Validation Framework**
   - Extract common validation context and error handling
   - Requires careful testing of all validators
   - Medium impact (~2K lines), high risk

### Long-Term Actions (High Risk)

5. **ISA Abstraction Layer**
   - Only attempt after Full Simple trait system is stable
   - Requires comprehensive testing on all platforms
   - Very high impact (~1.5K lines), very high risk

6. **Automated Desugaring**
   - Complete the desugaring pipeline
   - Eliminate compiler/ ↔ compiler_core/ duplication
   - Massive impact (~15K lines), requires full bootstrap redesign

---

## Duplication That Should NOT Be Removed

### 1. **compiler/ vs compiler_core/** (~15K lines)
- **Why:** Bootstrap requirement (Full Simple vs Core Simple)
- **Status:** Documented in READMEs (2026-02-11)

### 2. **Type Mappers** (6 files, ~1.5K lines)
- **Why:** Backend-specific type representations
- **Status:** Part of intentional compiler/compiler_core split

### 3. **Test Fixtures** (various)
- **Why:** Explicit test scenarios for different edge cases
- **Status:** Already cleaned up (493 files removed in previous phases)

---

## Metrics

### Current Duplication Estimate
- **Intentional (documented):** ~15,000 lines (compiler/compiler_core)
- **Phase files (development):** ~12,000 lines
- **Validators (structural):** ~2,000 lines
- **Builders (pattern):** ~500 lines
- **ISA encoders (cross-platform):** ~1,500 lines
- **Total addressable:** ~16,000 lines (excluding intentional duplication)

### Cleanup Progress
- **Phase 1-3 (2026-02-10):** 318 files removed
- **Phase 4 (2026-02-11):** Documentation added, intentional duplication explained
- **Total files removed:** 318
- **Documentation added:** 196 lines

---

## Tools Available

1. **`bin/simple duplicate-check`** - Built-in duplication detector
   - Karp-Rabin hash for exact duplicates
   - Cosine similarity for fuzzy matching
   - Note: Currently has issues with file collection (shell integration)

2. **Manual Analysis**
   - `grep -r "pattern" src/`
   - `find src/ -name "*.spl" -exec wc -l {}`
   - `diff -u file1 file2`

---

## Conclusion

The codebase has been cleaned of trivial duplications (test files) and intentional duplications have been documented. The remaining duplication falls into three categories:

1. **Development Evolution** (phase files) - Can be consolidated but low priority
2. **Structural Patterns** (validators, builders) - Could benefit from abstraction but high risk
3. **Cross-Platform Similarity** (ISA encoders) - Natural duplication that's hard to eliminate safely

**Recommendation:** Consider the cleanup **complete** for now. Focus on:
- Maintaining documentation
- Preventing new trivial duplications (pre-commit hooks)
- Addressing phase file consolidation as a separate low-priority task

Future work should focus on completing the desugaring pipeline to eliminate the ~15K lines of compiler/compiler_core duplication automatically.
