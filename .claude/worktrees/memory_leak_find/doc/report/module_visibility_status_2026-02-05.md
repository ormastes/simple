# Module Visibility Feature - Status Report

**Date:** 2026-02-05
**Reporter:** Claude
**Feature ID:** LANG-042
**Status:** 🟡 Planning Complete, Implementation Not Started

---

## Executive Summary

The module visibility feature is in the **design phase** with comprehensive planning completed but **zero implementation**. There are actually **two separate visibility systems** to consider:

1. **Existing System** (Implemented): Directory-based visibility with `pub mod` and `export` lists
2. **New System** (Planned): File-based visibility with `public`/`private` keywords and filename-based auto-public

**Key Finding:** These two systems have **different philosophies** and may need reconciliation.

---

## Current State Analysis

### ✅ What Exists

| Component | Status | Location | Notes |
|-----------|--------|----------|-------|
| **Design Document** | ✅ Complete | `doc/design/module_visibility_design.md` | 476 lines, comprehensive |
| **Test Specification** | ✅ Complete | `test/system/features/module_visibility/module_visibility_spec.spl` | 296 lines, 8 test groups, all `@pending` |
| **Existing Visibility** | ✅ Implemented | `src/compiler/dependency/visibility.spl` | Directory-based system (344 lines) |

### ❌ What's Missing

| Component | Status | Blocker |
|-----------|--------|---------|
| **Parser Support** | ❌ Not Started | No `public`/`private` keyword tokens |
| **Lexer Support** | ❌ Not Started | No `KwPublic`/`KwPrivate` tokens |
| **HIR Changes** | ❌ Not Started | No visibility tracking in HIR |
| **Type Checker** | ❌ Not Started | No visibility validation |
| **Top-level `val`** | ❌ Not Started | Parser doesn't allow module-level constants |
| **Filename Matching** | ❌ Not Started | No snake_case → PascalCase conversion |
| **Warning Generation** | ❌ Not Started | No W0401-W0404 warnings |
| **Feature DB Entry** | ❌ Missing | Not in `doc/feature/feature_db.sdn` |

---

## Two Visibility Systems Comparison

### System 1: Existing (Directory-Based)

**File:** `src/compiler/dependency/visibility.spl`

**Model:**
- Visibility controlled at **directory level** via `__init__.spl`
- Uses `pub mod child_module` to expose modules
- Uses `export` lists to expose symbols
- Three access policies: Open, Boundary, Bypass
- Formal verification with 7 Lean theorems

**Example:**
```simple
# In core/__init__.spl
pub mod test_case       # Makes test_case module public
export TestCase         # Exports TestCase type
export create_test      # Exports function
```

**Status:** ✅ Fully implemented and verified

### System 2: Proposed (File-Based)

**File:** `doc/design/module_visibility_design.md`

**Model:**
- Visibility controlled at **file level** with keywords
- Types matching filename are **auto-public** (snake_case → PascalCase)
- Everything else is **private by default**
- Uses `public`/`private` keywords for explicit control
- Enables **top-level `val` declarations**

**Example:**
```simple
# In test_case.spl

# Auto-public: name matches filename
class TestCase:
    id: i32

# Private by default
class Helper:
    data: i32

# Explicit public
public fn create_test() -> TestCase:
    TestCase(id: 0)

# Module-level constant (private)
val DEFAULT_ID: i32 = 0
```

**Status:** ❌ Design only, not implemented

---

## Design Analysis

### Design Document Quality: ⭐⭐⭐⭐⭐

The design document (`doc/design/module_visibility_design.md`) is **exceptional quality**:

✅ **Strengths:**
- Clear problem statement with concrete examples
- Well-defined rules and edge cases
- Complete implementation plan (36h estimate, 7 phases)
- Rollout timeline (v0.5.0 → v1.0.0)
- Warning/error code specification (W0401-W0404, E0403-E0404)
- Migration tool specification
- FAQ section
- Alternatives considered section
- Before/after examples

📊 **Structure:**
- 9 major sections
- 15 code examples
- 8 comparison tables
- 476 lines total

### Test Specification Quality: ⭐⭐⭐⭐⭐

The test spec (`module_visibility_spec.spl`) is **comprehensive**:

✅ **Coverage:**
- 8 test groups covering all aspects
- 28+ individual test cases (all marked `skip`)
- Follows SSpec BDD format
- Clear documentation strings
- Edge cases included

📊 **Test Groups:**
1. Filename-Based Auto-Public (3 tests)
2. Explicit Visibility Keywords (4 tests)
3. Top-Level Val Declarations (4 tests)
4. Impl Block Visibility (3 tests)
5. Warnings and Errors (4 tests)
6. Module Re-exports (3 tests)
7. Import Integration (3 tests)
8. Edge Cases (4 tests)

---

## Integration Challenges

### 🔴 Critical Issue: Two Systems Coexist

The codebase will have **two visibility mechanisms** simultaneously:

| Aspect | Directory System | File System |
|--------|-----------------|-------------|
| **Scope** | Module directory | Individual file |
| **Default** | Depends on `__init__.spl` | Private (except filename match) |
| **Keywords** | `pub mod`, `export` | `public`, `private` |
| **Granularity** | Coarse (whole modules) | Fine (per declaration) |
| **Philosophy** | Explicit exports | Implicit with overrides |

**Questions to Resolve:**
1. Do both systems operate simultaneously?
2. Does file-based visibility override directory-based?
3. How do `export` lists interact with `public` keywords?
4. What happens when a file has `public class Foo` but directory doesn't export it?

**Recommendation:** Need **integration design document** to reconcile these systems.

---

## Implementation Roadmap

### Phase 0: Reconciliation (NEW - Not in Original Plan)

**Estimated Effort:** 8h design + 4h documentation

1. **Design Integration Strategy**
   - Decide interaction between directory and file visibility
   - Define precedence rules
   - Update both design documents

2. **Update Documentation**
   - Add integration section to `module_visibility_design.md`
   - Document interaction patterns
   - Add examples showing both systems

### Phase 1: Lexer/Parser Changes

**Estimated Effort:** 8h (4h lexer + 4h parser)

**Original estimate:** 4h (parser only)
**Updated estimate:** 8h (missed lexer work)

**Tasks:**
1. Add `KwPublic` and `KwPrivate` tokens to lexer
2. Parse visibility modifiers on:
   - `class` declarations
   - `struct` declarations
   - `enum` declarations
   - `fn` declarations
   - `val` declarations (new!)
   - `var` declarations
   - `type` aliases
3. Enable top-level `val`/`var` parsing
4. Update AST to include visibility field

**Files to Modify:**
- Lexer token definitions
- Parser declaration rules
- AST node structures

### Phase 2: HIR Representation

**Estimated Effort:** 8h

**Tasks:**
1. Add `Visibility` enum to HIR types
2. Track visibility on all relevant HIR nodes
3. Update HIR lowering from AST
4. Preserve visibility through compilation passes

**Files to Modify:**
- HIR type definitions
- AST → HIR lowering

### Phase 3: Filename Matching Logic

**Estimated Effort:** 4h

**Tasks:**
1. Implement `filename_to_type_name()` conversion
   - `test_case.spl` → `TestCase`
   - `string_interner.spl` → `StringInterner`
   - Handle edge cases (single-word, acronyms)
2. Add tests for conversion logic
3. Integrate into type resolution

**Algorithm:**
```
filename_to_type(name):
    1. Remove .spl extension
    2. Split by underscore
    3. Capitalize first letter of each part
    4. Join without separator
```

### Phase 4: Type Checker Integration

**Estimated Effort:** 8h

**Tasks:**
1. Track effective visibility for each symbol
2. Check visibility at use sites
3. Validate access from importing modules
4. Special handling for `mod.spl` files
5. Impl block visibility rules

**Files to Modify:**
- Type checker symbol resolution
- Import resolution
- Access validation

### Phase 5: Warning Generation (Phase 1 Warnings)

**Estimated Effort:** 4h

**Tasks:**
1. Implement warning codes:
   - `W0401`: Implicitly public type (name doesn't match file)
   - `W0402`: Implicitly public function
   - `W0403`: Implicitly public constant
   - `W0404`: Redundant visibility modifier
2. Add help messages with suggestions
3. Configure as warnings (not errors) initially

### Phase 6: Error Generation (Phase 2 Errors)

**Estimated Effort:** 4h

**Tasks:**
1. Implement error codes:
   - `E0403`: Accessing private item from outside module
   - `E0404`: Cannot make filename-matching type private
2. Add diagnostic messages
3. Add fix suggestions

### Phase 7: Migration Tooling

**Estimated Effort:** 8h

**Tasks:**
1. Implement `simple lint --check-visibility`
2. Implement `simple fix --add-visibility`
3. Add `--dry-run` flag for preview
4. Handle edge cases and bulk operations

### Phase 8: Testing & Documentation

**Estimated Effort:** 12h

**Tasks:**
1. Activate all tests in `module_visibility_spec.spl`
2. Add integration tests
3. Test interaction with existing directory system
4. Update user-facing documentation
5. Write migration guide

---

## Total Effort Estimate

| Phase | Original Estimate | Updated Estimate | Difference |
|-------|------------------|------------------|------------|
| 0. Reconciliation | Not planned | **12h** | +12h |
| 1. Lexer/Parser | 4h | **8h** | +4h |
| 2. HIR | 8h | **8h** | — |
| 3. Filename Match | 4h | **4h** | — |
| 4. Type Checker | 8h | **8h** | — |
| 5. Warnings | 4h | **4h** | — |
| 6. Errors | 4h | **4h** | — |
| 7. Migration Tool | Not planned | **8h** | +8h |
| 8. Testing | Not planned | **12h** | +12h |
| **Total** | **36h** | **68h** | **+32h** |

**Original estimate was optimistic.** Realistic estimate is **68 hours** (1.9x longer).

**Breakdown by complexity:**
- 🟢 Low Risk: 16h (Phases 3, 5, 6)
- 🟡 Medium Risk: 32h (Phases 1, 2, 4, 7)
- 🔴 High Risk: 20h (Phases 0, 8 - require design decisions)

---

## Rollout Timeline (Proposed)

| Version | Changes | Status |
|---------|---------|--------|
| **v0.5.0** | Parse `public`/`private` keywords (warnings only) | 🔴 Blocked |
| **v0.6.0** | Enable top-level `val` (private default) | 🔴 Blocked |
| **v0.7.0** | Emit W0401-W0404 warnings for implicit visibility | 🔴 Blocked |
| **v0.8.0** | Migration tool available | 🔴 Blocked |
| **v1.0.0** | Private by default (E0403-E0404 errors active) | 🔴 Blocked |

All blocked on Phase 0 reconciliation.

---

## Related Features

### 🔗 Dependencies

| Feature | Relationship | Status |
|---------|-------------|--------|
| **Directory Visibility** | Co-exists with new system | ✅ Implemented |
| **Module Resolution** | Must understand file visibility | ✅ Implemented |
| **Type Checker** | Validates visibility access | ✅ Exists (needs extension) |
| **Import System** | Respects visibility rules | ✅ Exists (needs extension) |

### 🔗 Related Test Specs

| Spec | Feature ID | Relationship |
|------|-----------|-------------|
| `visibility_modifiers_spec.spl` | TBD | General visibility (may overlap) |
| `module_visibility_spec.spl` | LANG-042 | This feature |

**Note:** Two separate test directories exist. May need consolidation.

---

## Recommendations

### Immediate Actions (Priority 1)

1. ✅ **Add LANG-042 to Feature Database**
   - Create feature entry in `doc/feature/feature_db.sdn`
   - Link to design doc and test spec
   - Mark as "Planned" status

2. 🔴 **Write Integration Design Document**
   - Address interaction between directory and file visibility
   - Define precedence rules
   - Add examples
   - Get stakeholder review

3. 🟡 **Consolidate Test Specs**
   - Merge `visibility_modifiers_spec.spl` into `module_visibility_spec.spl`
   - Or clarify their distinct purposes
   - Update feature IDs

### Short-Term (Priority 2)

4. **Prototype Lexer/Parser Changes**
   - Implement `KwPublic`/`KwPrivate` tokens
   - Enable parsing (no semantics yet)
   - Validate syntax in simple examples

5. **Implement Filename Matching**
   - Small, self-contained feature
   - Can be tested independently
   - Builds confidence

### Long-Term (Priority 3)

6. **Incremental Rollout**
   - Follow the v0.5.0 → v1.0.0 plan
   - Start with warnings only
   - Give users time to migrate
   - Activate errors in v1.0.0

7. **Migration Automation**
   - Build `simple fix --add-visibility` tool
   - Auto-detect and fix visibility issues
   - Critical for adoption

---

## Risk Assessment

### High Risks 🔴

1. **Two Systems Conflict**
   - Directory vs. file visibility
   - Users confused about which takes precedence
   - **Mitigation:** Clear documentation and integration design

2. **Breaking Changes**
   - Existing code assumes all public
   - Making things private breaks imports
   - **Mitigation:** Warning period (2-3 versions)

3. **Top-Level `val` Complications**
   - Currently unsupported
   - May have parser/type-checker implications
   - **Mitigation:** Prototype early, validate approach

### Medium Risks 🟡

4. **Filename Matching Edge Cases**
   - Acronyms: `http_api.spl` → `HttpApi` or `HTTPAPI`?
   - Single words: `io.spl` → `Io` or `IO`?
   - **Mitigation:** Clear rules, good test coverage

5. **Migration Tool Complexity**
   - Analyzing visibility can be complex
   - False positives/negatives
   - **Mitigation:** Dry-run mode, conservative defaults

### Low Risks 🟢

6. **Warning Fatigue**
   - Many warnings initially
   - Users may ignore
   - **Mitigation:** Clear, actionable messages with auto-fix

---

## Success Metrics

### Implementation Success

- [ ] All 28 tests in `module_visibility_spec.spl` passing
- [ ] Zero `skip` markers in test suite
- [ ] Feature marked "Complete" in feature database
- [ ] All compiler phases support visibility

### User Adoption Success

- [ ] Migration tool successfully runs on stdlib
- [ ] Documentation examples use new syntax
- [ ] Less than 5% of users report confusion
- [ ] Build times not impacted (< 1% slowdown)

### Code Quality Success

- [ ] No visibility-related bugs in first 3 months
- [ ] Formal verification (Lean theorems) integrated
- [ ] Test coverage > 90% for visibility logic
- [ ] Clear error messages (user testing)

---

## Appendix: File Inventory

### Design Documentation

| File | Lines | Status | Quality |
|------|-------|--------|---------|
| `doc/design/module_visibility_design.md` | 476 | ✅ Complete | ⭐⭐⭐⭐⭐ |

### Test Specifications

| File | Lines | Tests | Status |
|------|-------|-------|--------|
| `test/system/features/module_visibility/module_visibility_spec.spl` | 296 | 28 | All `@pending` |
| `test/system/features/visibility_modifiers/visibility_modifiers_spec.spl` | 27 | 1 | Placeholder only |

### Implementation Files

| File | Lines | Purpose | Status |
|------|-------|---------|--------|
| `src/compiler/dependency/visibility.spl` | 344 | Directory visibility (old system) | ✅ Implemented |
| Lexer token definitions | ? | Token types | ❌ Missing `KwPublic`/`KwPrivate` |
| Parser declarations | ? | Parse visibility modifiers | ❌ Not started |
| HIR types | ? | Track visibility | ❌ Not started |
| Type checker | ? | Validate visibility | ❌ Not started |

---

## Next Steps

**For Project Lead:**
1. Review this report
2. Decide on two-system integration approach
3. Prioritize LANG-042 in roadmap
4. Assign implementation to developer(s)

**For Developer:**
1. Read design document thoroughly
2. Start with Phase 0 (reconciliation)
3. Prototype lexer/parser changes
4. Regular check-ins on progress

**For Documentation:**
1. Add LANG-042 to feature tracking
2. Update roadmap with timeline
3. Create user-facing migration guide (draft)

---

## Conclusion

The module visibility feature is **thoroughly planned** but **not yet implemented**. The design quality is excellent, but there's a critical need to reconcile the new file-based system with the existing directory-based system.

**Estimated completion time:** 68 hours (8.5 developer-days)
**Earliest realistic delivery:** 2-3 weeks (assuming full-time work)
**Recommended timeline:** Include in v0.6.0 or v0.7.0 milestone

The feature is **ready to implement** once the integration strategy is finalized.

---

**Report Status:** ✅ Complete
**Last Updated:** 2026-02-05
**Next Review:** After Phase 0 reconciliation
