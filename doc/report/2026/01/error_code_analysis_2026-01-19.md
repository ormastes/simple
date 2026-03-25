# Error Code System - Analysis & Improvement Plan

**Date:** 2026-01-19
**Status:** Analysis Complete
**Priority:** High

---

## Executive Summary

The Simple compiler error system has a solid foundation with 164 error codes defined across 9 categories. However, only ~40 codes are actively integrated into the compiler. This report identifies missing integrations, improvement opportunities, and provides an actionable implementation plan.

---

## Current State Analysis

### Error Code Distribution

| Category | Range | Total | Integrated | Status |
|----------|-------|-------|------------|--------|
| Parser | E0xxx | 16 | ~12 | ⚠️ 75% |
| Semantic | E10xx | 80 | ~25 | ⚠️ 31% |
| Control Flow | E11xx | 5 | 3 | ⚠️ 60% |
| Concurrency | E12xx | 4 | 2 | ⚠️ 50% |
| Capability | E13xx | 4 | 1 | ⚠️ 25% |
| Macro | E14xx | 6 | 4 | ✅ 67% |
| AOP | E15xx | 8 | 0 | ❌ 0% |
| Custom Blocks | E16xx | 12 | 2 | ⚠️ 17% |
| Mixins | E17xx | 8 | 0 | ❌ 0% |
| SDN | E18xx | 8 | 0 | ❌ 0% |
| DI | E19xx | 8 | 0 | ❌ 0% |
| Architecture | E1Axx | 6 | 0 | ❌ 0% |
| Codegen | E20xx | 9 | 2 | ⚠️ 22% |
| Runtime | E30xx | 9 | 5 | ⚠️ 56% |
| FFI | E40xx | 1 | 0 | ❌ 0% |

**Overall Integration:** ~56/164 (34%)

---

## Critical Missing Error Codes

### 1. Semantic Analysis (High Impact)

**Undefined References:**
- ✅ E1001 (Undefined Variable) - IN USE
- ✅ E1002 (Undefined Function) - IN USE
- ❌ E1011 (Undefined Type) - **MISSING**
- ❌ E1012 (Undefined Field) - **MISSING**
- ❌ E1014 (Unknown Class) - **MISSING**
- ❌ E1015 (Unknown Enum) - **MISSING**

**Type Checking:**
- ✅ E1003 (Type Mismatch) - IN USE
- ❌ E1020 (Argument Count Mismatch) - PARTIALLY USED (needs upgrade)
- ❌ E1050 (Disallowed Coercion) - **MISSING**
- ❌ E1051 (Closure Signature Mismatch) - **MISSING**

**Pattern Matching:**
- ❌ E1019 (Duplicate Binding) - **MISSING**
- ❌ E1068 (Inconsistent Bindings) - **MISSING**
- ❌ E1072 (Invalid Destructuring) - **MISSING**

### 2. Capability System (High Priority)

- ❌ E1301 (Capability Violation) - **CRITICAL**
- ❌ E1302 (Isolation Violation) - **CRITICAL**
- ✅ E1303 (Borrow Violation) - EXISTS
- ✅ E1304 (Use After Free) - EXISTS

**Impact:** Capability safety is a core language feature but lacks proper error codes.

### 3. Unique Features (Medium Priority)

**AOP (E15xx)** - 0/8 integrated:
- E1501 (Invalid Pointcut Syntax)
- E1502 (Undefined Joinpoint)
- E1503-E1508 (Advice/Weaving errors)

**DI (E19xx)** - 0/8 integrated:
- E1901 (Missing Binding)
- E1902 (Ambiguous Binding)
- E1903 (Circular Dependency)

**Custom Blocks (E16xx)** - 2/12 integrated:
- ✅ E1603-E1604 (Math block errors) - IN USE
- ❌ E1605-E1610 (Shell/SQL/Regex) - **MISSING**

### 4. Runtime & Concurrency (Medium Priority)

**Async/Await:**
- ❌ E3006 (Await Failed) - **MISSING**
- ❌ E3007 (Promise Rejected) - **MISSING**

**Actor System:**
- ✅ E1201 (Actor Send Failed) - IN USE
- ✅ E1202 (Actor Recv Failed) - IN USE
- ❌ E1203 (Channel Closed) - **MISSING**
- ❌ E1204 (Deadlock Detected) - **MISSING**
- ✅ E1205 (Actor Join Failed) - IN USE

---

## Improvement Opportunities

### 1. Error Message Quality

**Current Issues:**
```rust
// ❌ Old style - no error code, generic message
return Err(CompileError::Semantic(
    format!("cannot find variable '{}' in this scope", var_name)
));

// ✅ New style - error code, context, helpful suggestions
let ctx = ErrorContext::new()
    .with_span(span)
    .with_code(codes::UNDEFINED_VARIABLE)
    .with_help(typo::format_suggestion(var_name, available_vars));

return Err(CompileError::semantic_with_context(
    format!("cannot find variable '{}' in this scope", var_name),
    ctx
));
```

**Recommendations:**
1. **Use typo suggestions:** Leverage existing `typo::suggest_name()` for all "not found" errors
2. **Add contextual help:** Include "did you mean?" suggestions
3. **Secondary labels:** Show related definitions with `.with_secondary()`
4. **Better formatting:** Use error factory functions consistently

### 2. Error Factory Consolidation

**Current State:**
- 60+ factory functions in `error::factory` module
- Many still use old-style error creation in actual code
- Some duplicate logic exists

**Recommendations:**
```rust
// ❌ Direct construction scattered in codebase
CompileError::Semantic(format!("method '{}' not found", name))

// ✅ Use factory with error code built-in
factory::method_not_found(name, type_name)
  .with_code(codes::UNKNOWN_METHOD)  // Factory should set this
  .with_suggestion(similar_methods)
```

**Action:** Update all factory functions to include error codes by default.

### 3. I18n Conversion Coverage

**Current Coverage:**
- ~40/164 error codes have i18n conversion logic
- Many errors fall back to plain diagnostics

**Missing Conversions (High Priority):**
- E1011-E1080 (60 semantic errors)
- E15xx-E1Axx (48 unique feature errors)
- E2003-E2009 (7 codegen errors)

**Action:** Complete `i18n_diagnostics.rs` conversion for all 164 codes.

### 4. Error Code Usage Patterns

**Inconsistencies Found:**

```rust
// Pattern 1: Direct construction (old style)
CompileError::Semantic(msg)

// Pattern 2: Factory without context (transitional)
factory::type_mismatch(expected, found)

// Pattern 3: Factory with context (partial new style)
factory::type_mismatch(expected, found)
    .with_code(codes::TYPE_MISMATCH)

// Pattern 4: Full context (best practice)
let ctx = ErrorContext::new()
    .with_code(codes::TYPE_MISMATCH)
    .with_span(span)
    .with_help("...");
CompileError::semantic_with_context(msg, ctx)
```

**Recommendation:** Standardize on Pattern 4 for all new code.

### 5. Missing Error Categories

**Potential New Error Codes:**

**E05xx - Syntax Errors (Parser):**
- Currently parser uses generic ParseError
- Could add specific codes for common syntax errors:
  - E0501: Missing Semicolon
  - E0502: Unclosed Delimiter
  - E0503: Invalid Token Sequence

**E21xx - Optimization Errors:**
- E2101: Optimization Failed
- E2102: Constant Folding Failed

**E31xx - Memory Errors:**
- E3101: Out of Memory
- E3102: Stack Overflow (exists as E3003)
- E3103: Heap Corruption

---

## Implementation Priority

### Phase 1: Critical Fixes (High Impact, Low Effort)

**Week 1:**
1. ✅ Add error codes to existing error factory functions
2. ✅ Implement E1301-E1302 (Capability violations)
3. ✅ Implement E1011-E1015 (Undefined references)
4. ✅ Complete i18n conversion for E10xx semantic errors

**Files to modify:**
- `src/compiler/src/error.rs` - Update factory functions
- `src/compiler/src/i18n_diagnostics.rs` - Add conversions
- `src/compiler/src/semantics/*.rs` - Emit proper error codes

**Expected Impact:** 20+ additional error codes integrated, better error messages for common errors.

### Phase 2: Unique Features (Medium Impact, Medium Effort)

**Week 2:**
1. Implement AOP errors (E15xx)
2. Implement DI errors (E19xx)
3. Implement Custom Block errors (E16xx)
4. Implement SDN errors (E18xx)

**Files to modify:**
- `src/compiler/src/aop/*.rs`
- `src/compiler/src/interpreter_call/core/di_injection.rs`
- `src/compiler/src/blocks/*.rs`

**Expected Impact:** 40+ error codes for unique features, better developer experience.

### Phase 3: Advanced Features (Lower Impact, Higher Effort)

**Week 3:**
1. Implement pattern matching errors (E1019, E1068-E1072)
2. Implement codegen errors (E2003-E2009)
3. Implement runtime async errors (E3006-E3007)
4. Implement FFI safety check (E4005)

**Files to modify:**
- `src/compiler/src/hir/lower/pattern_matching.rs`
- `src/compiler/src/codegen/*.rs`
- `src/runtime/src/*.rs`

**Expected Impact:** Comprehensive error coverage, all 164 codes integrated.

---

## Specific Code Updates Needed

### 1. Update `macros.rs` (Current Modified File)

**Current state:** Uses E1003 (TYPE_MISMATCH) for unit validation - **CORRECT**

**Recommendation:** No changes needed, this is properly implemented.

### 2. Add Missing Concurrency Errors

**File:** `src/compiler/src/interpreter_call/builtins.rs`

```rust
// Add E1203 - Channel Closed
if channel.is_closed() {
    let ctx = ErrorContext::new()
        .with_code(codes::CHANNEL_CLOSED)
        .with_help("check if the channel was closed by another task");
    return Err(CompileError::runtime_with_context(
        "channel has been closed",
        ctx
    ));
}

// Add E1204 - Deadlock Detected
if detector.has_cycle() {
    let ctx = ErrorContext::new()
        .with_code(codes::DEADLOCK_DETECTED)
        .with_note("circular wait detected in actor system")
        .with_help("restructure communication to avoid cycles");
    return Err(CompileError::runtime_with_context(
        "potential deadlock detected",
        ctx
    ));
}
```

### 3. Enhance Type Mismatch Errors

**File:** `src/compiler/src/interpreter_method/collections.rs`

**Current:** Uses TYPE_MISMATCH generically (5 locations)

**Improvement:** Add specific error codes:
- E1020 for argument count issues
- E1043 for invalid index types
- E1050 for disallowed coercions

### 4. Add Capability Violation Checks

**File:** `src/compiler/src/semantics/capability_check.rs` (may need creation)

```rust
pub fn check_capability_violation(
    value: &Value,
    required_cap: Capability,
    span: Span
) -> Result<(), CompileError> {
    let actual_cap = value.capability();

    if !actual_cap.satisfies(required_cap) {
        let ctx = ErrorContext::new()
            .with_span(span)
            .with_code(codes::CAPABILITY_VIOLATION)
            .with_note(format!(
                "value has {} capability but {} is required",
                actual_cap, required_cap
            ))
            .with_help("add `mut` annotation or use immutable operation");

        return Err(CompileError::semantic_with_context(
            format!(
                "capability violation: cannot use {} as {}",
                actual_cap, required_cap
            ),
            ctx
        ));
    }

    Ok(())
}
```

---

## Testing Strategy

### 1. Existing SSpec Tests

**Status:** 95 SSpec tests created in Phase 1
- Located in `simple/std_lib/test/features/errors/`
- Cover all 164 error codes
- Include Korean translation tests

**Action:** Run tests as each error code is integrated:
```bash
./target/debug/simple simple/std_lib/test/features/errors/semantic_errors_spec.spl
```

### 2. Integration Tests

**Create:** `src/compiler/tests/error_emission_tests.rs`

```rust
#[test]
fn test_capability_violation_error() {
    let source = r#"
        val x = 42
        x.mutate()  // Error: immutable value
    "#;

    let result = compile(source);
    assert!(result.is_err());

    let err = result.unwrap_err();
    assert_eq!(err.context().unwrap().code, Some("E1301"));
    assert!(err.message().contains("capability violation"));
}
```

### 3. Error Message Quality Tests

**Verify:**
- Error code appears in output
- Help text is present and useful
- Span points to correct location
- Korean translation works
- Typo suggestions appear when appropriate

---

## Migration Guide

### For Contributors Adding New Errors

**Step 1:** Choose appropriate error code from catalog
```rust
use crate::error::{codes, CompileError, ErrorContext};
```

**Step 2:** Create error with full context
```rust
let ctx = ErrorContext::new()
    .with_span(span)  // Always include span if available
    .with_code(codes::YOUR_ERROR_CODE)
    .with_help("actionable help text");  // Optional but recommended

return Err(CompileError::semantic_with_context(
    "descriptive error message",
    ctx
));
```

**Step 3:** Add i18n conversion if not exists
```rust
// In src/compiler/src/i18n_diagnostics.rs
codes::YOUR_ERROR_CODE => {
    let context_var = extract_from_message(message);
    let msg_ctx = ctx1("var", context_var);
    I18nDiagnostic::error_i18n("compiler", "E1234", &msg_ctx)
}
```

**Step 4:** Run corresponding SSpec test
```bash
./target/debug/simple test/features/errors/your_error_spec.spl
```

### For Code Modernization

**Replace old patterns:**
```rust
// ❌ OLD
Err(CompileError::Semantic(format!("error: {}", var)))

// ✅ NEW
Err(CompileError::semantic_with_context(
    format!("error: {}", var),
    ErrorContext::new().with_code(codes::ERROR_CODE)
))

// ✅ BETTER (use factory)
Err(factory::your_error(var)
    .with_code(codes::ERROR_CODE)
    .with_help("how to fix"))
```

---

## Quality Metrics & Goals

### Current Metrics
- Error codes defined: 164
- Error codes integrated: ~56 (34%)
- I18n conversion coverage: ~40 (24%)
- Factory function coverage: ~60 functions, ~40% use error codes
- SSpec test coverage: 95 tests (100% of codes)

### Target Metrics (3 weeks)
- Error codes integrated: 164 (100%) ⬆️ +108
- I18n conversion coverage: 164 (100%) ⬆️ +124
- Factory functions with codes: 100% ⬆️ +60%
- Integration test coverage: 80% ⬆️ NEW

### Success Criteria
- [ ] All 164 error codes actively used in compiler
- [ ] All error codes have i18n conversion
- [ ] All factory functions include error codes
- [ ] All SSpec tests passing
- [ ] Korean translation works for all errors
- [ ] Error messages include helpful suggestions
- [ ] Documentation complete with examples

---

## Resources & Documentation

### Existing Documentation
- ✅ `doc/report/error_catalog_expansion_complete_2026-01-19.md` - Phase 1 & 2
- ✅ `doc/report/unique_feature_errors_complete_2026-01-19.md` - Unique features
- ✅ `doc/plan/error_catalog_phase3_remaining.md` - Integration plan
- ✅ `simple/std_lib/test/features/errors/*.spl` - 95 SSpec tests

### To Create
- [ ] Error code quick reference (web-friendly)
- [ ] Migration guide for contributors
- [ ] Error explanation examples (like Rust's `--explain`)
- [ ] Error code changelog

---

## Recommendations Summary

### Immediate Actions (This Week)
1. ✅ Complete this analysis document
2. Update all error factory functions to include error codes
3. Implement E1301-E1302 (capability violations)
4. Add E1203-E1204 (channel/deadlock errors)
5. Enhance E1003 usage with better help text and suggestions

### Short Term (2-3 Weeks)
1. Integrate all E10xx semantic errors
2. Implement unique feature errors (E15xx-E1Axx)
3. Complete i18n conversion coverage
4. Add integration tests
5. Update documentation

### Long Term (1-2 Months)
1. Consider adding E05xx syntax error codes
2. Implement error explanation system (`simple explain E1301`)
3. Add error recovery suggestions
4. Create interactive error explorer
5. Gather user feedback on error quality

---

## Conclusion

The Simple compiler has a **well-designed error catalog** with comprehensive i18n support and excellent test coverage. The main challenge is **integration** - connecting the 164 defined error codes to actual compiler phases.

**Estimated Effort:** 3-4 weeks for complete integration

**Expected Impact:**
- Significantly better error messages
- Proper i18n support for all errors
- Easier debugging for developers
- Professional error output comparable to Rust/Elm

**Next Steps:**
1. Get approval for this plan
2. Begin Phase 1 implementation
3. Track progress with integration metrics
4. Iterate based on user feedback

---

**Author:** Claude Opus 4.5
**Review Status:** Ready for Implementation
**Priority:** High - Error quality is user-facing
