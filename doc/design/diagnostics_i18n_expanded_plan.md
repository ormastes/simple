# Diagnostics I18n Expanded Implementation Plan

**Date**: 2026-01-19
**Status**: Phase 1 Complete, Planning Phase 1B (Expansion)
**Based on**: Rust-to-Simple error mapping analysis
**Goal**: Expand Simple's error catalog from 80 to 164 codes

---

## Executive Summary

After analyzing Rust's ~500 error codes, we've identified **84 new error codes** that are applicable to Simple. Combined with the existing 80 codes, this brings Simple's total to **164 error codes**, covering ~32% of Rust's error space while maintaining Simple's design philosophy.

**Key Finding**: ~60% of Rust's errors (lifetimes, borrow checker, unsafe, const generics) are **not applicable** to Simple due to GC-based memory model and different language design.

---

## Current Status (After Phase 1)

**Completed**:
- ✅ 80 error codes cataloged (E0001-E6204)
- ✅ 100% Korean translation coverage
- ✅ Build system integrated
- ✅ Comprehensive Rust mapping analysis

**Next**:
- 📋 Add 84 new error codes (E0013-E0016, E1019-E1080, etc.)
- 📋 Create SSpec tests for all new errors
- 📋 Extend catalogs with Korean translations
- 📋 Document feature requirements

---

## Phase 1B: Catalog Expansion (NEW)

### Goal
Extend error catalogs with 84 new error codes identified from Rust mapping.

### New Error Codes by Category

#### Parser Errors (E0013-E0016) +4 codes

| Code | Name | Description | Priority |
|------|------|-------------|----------|
| E0013 | Invalid Range Pattern | Invalid range in pattern matching | Medium |
| E0014 | Invalid Literal Pattern | Invalid literal in pattern | Medium |
| E0015 | Unterminated Attribute | Attribute syntax not closed | High |
| E0016 | Expected Item | Expected item, found token | High |

#### Compiler Semantic Errors (E1019-E1080) +62 codes

**Pattern & Binding (E1019)**:
- E1019: Duplicate Binding - Duplicate binding in pattern

**Function Call Errors (E1020-E1024)**:
- E1020: Argument Count Mismatch - Wrong number of arguments
- E1021: Missing Struct Fields - Required fields missing in struct literal
- E1022: Invalid LHS Assignment - Invalid left-hand side of assignment
- E1023: Invalid Struct Literal - Struct literal syntax error
- E1024: Const Eval Failed - Constant evaluation failed

**Trait & Impl Errors (E1025-E1031)**:
- E1025: Duplicate Method - Duplicate method in impl block
- E1026: Unknown Assoc Type - Associated type not in trait
- E1027: Unconstrained Type Param - Type parameter not constrained
- E1028: Unknown Assoc Type - Unknown associated type name
- E1029: Conflicting Trait Bounds - Multiple conflicting trait bounds
- E1030: Invalid Lifetime on Trait - Lifetime parameter invalid on trait
- E1031: Missing Trait Method - Required trait method not implemented

**Module & Visibility (E1032-E1040)**:
- E1032: Self in Static - `self` used in static context
- E1033: Invalid Self Import - Invalid `self` in import path
- E1034: Unresolved Import - Import path not found
- E1035: Invalid Self Context - `self` in invalid context
- E1036: Closure Capture Failed - Cannot capture variable in closure
- E1037: Invalid Self Param - Invalid `self` parameter type
- E1038: Private in Public - Private type in public interface
- E1039: Invalid Visibility - Visibility qualifier not allowed
- E1040: Private Field Access - Field is private

**Operators & Casting (E1041-E1044)**:
- E1041: Invalid Unary Op - Cannot apply unary operator to type
- E1042: Invalid Self Type - `Self` type in invalid context
- E1043: Invalid Index Type - Index must be integer
- E1044: Tuple Index OOB - Tuple index out of range

**Field & Method Access (E1045-E1048)**:
- E1045: Invalid Field Assign - Cannot assign to non-field
- E1046: Private Field - Field is private
- E1047: Cannot Borrow Mut Field - Cannot borrow field as mutable
- E1048: Not Callable - Type is not callable

**Closures (E1049-E1052)**:
- E1049: Cannot Call Non-Function - Cannot call non-function type
- E1050: Disallowed Coercion - Type coercion not allowed
- E1051: Closure Signature Mismatch - Closure signature doesn't match
- E1052: Invalid Let-Else Pattern - Reference in let-else pattern

**Mutability & References (E1053-E1054)**:
- E1053: Cannot Borrow Immutable - Cannot create mutable ref to immutable
- E1054: Invalid Deref - Cannot dereference type

**Generics & Types (E1055-E1065)**:
- E1055: Type Alias Bounds - Type alias cannot have bounds
- E1056: Invalid Range - Invalid range expression
- E1057: Yield Outside Generator - `yield` outside generator
- E1058: Invalid Doc Comment - Doc comment in invalid location
- E1059: Invalid Implicit Deref - Cannot implicitly dereference
- E1060: Invalid Const Expression - Expression not valid in const
- E1061: Empty Enum - Enum must have variants
- E1062: Recursion Limit - Recursion limit exceeded
- E1063: Type Size Limit - Type size limit exceeded
- E1064: Wrong Intrinsic Type - Intrinsic requires different type
- E1065: Invalid Return Type - Function return type error

**Compilation & Attributes (E1066-E1080)**:
- E1066: Invalid Main Signature - Invalid `main` function signature
- E1067: Invalid Builtin Attr - Invalid use of built-in attribute
- E1068: Inconsistent Bindings - Inconsistent bindings in pattern
- E1069: Mismatched Binding - Variable binding mismatch
- E1070: Invalid Default Variant - Invalid `#[default]` on variant
- E1071: Invalid Attr Position - Attribute not allowed here
- E1072: Invalid Destructuring - Invalid destructuring assignment
- E1073: Non-Exhaustive Type - Cannot construct non-exhaustive type
- E1074: Conflicting Repr - Conflicting representation attributes
- E1075: Discriminant Overflow - Enum discriminant overflow
- E1076: Unknown Intrinsic - Unknown compiler intrinsic
- E1077: Wrong Intrinsic Signature - Intrinsic has wrong signature
- E1078: Invalid Intrinsic Return - Intrinsic return type wrong
- E1079: Missing Generic Args - Missing generic arguments
- E1080: Type Too Complex - Type complexity limit

#### Control Flow (E1104-E1105) +2 codes

- E1104: Return in Closure - `return` used in closure
- E1105: Invalid Control Flow - Invalid control flow in context

#### Capability Errors (E1301-E1302) +2 codes - NEW CATEGORY

- E1301: Capability Violation - Trying to mutate immutable capability
- E1302: Isolation Violation - Aliasing isolated reference

#### Macro Errors (E1403) +1 code

- E1403: Keyword in Macro - Reserved keyword in macro

#### FFI Errors (E4005) +1 code

- E4005: Type Not FFI-Safe - Type is not FFI-safe

**Total New Errors**: 84 codes
**Total After Expansion**: 164 codes (80 existing + 84 new)

---

## Phase 1B Tasks

### Task 1: Extend English Catalogs (2-3 hours)

**Files to Update**:
- `i18n/parser.spl` - Add E0013-E0016
- `i18n/compiler.spl` - Add E1019-E1080, E1104-E1105, E1301-E1302, E1403
- `i18n/runtime.spl` - Add E4005

**Example Entry**:
```simple
"E1020": {
    "id": "E1020",
    "title": "Argument Count Mismatch",
    "message": "function expects {expected} argument(s), but {found} were provided",
    "label": "expected {expected} arguments",
    "help": "check the function signature and provide the correct number of arguments"
}
```

### Task 2: Create Korean Translations (3-4 hours)

**Files to Update**:
- `i18n/parser.ko.spl` - Add E0013-E0016
- `i18n/compiler.ko.spl` - Add E1019-E1080, E1104-E1105, E1301-E1302, E1403
- `i18n/runtime.ko.spl` - Add E4005

**Translation Guidelines**:
- Use formal polite form (합니다체)
- Proper particles: "이(가)", "을(를)", "에", "으로"
- Consistent terminology

**Example Translation**:
```simple
"E1020": {
    "id": "E1020",
    "title": "인수 개수 불일치",
    "message": "함수는 {expected}개의 인수를 기대하지만 {found}개가 제공되었습니다",
    "label": "{expected}개의 인수를 기대합니다",
    "help": "함수 시그니처를 확인하고 올바른 개수의 인수를 제공하세요"
}
```

### Task 3: Update Build Script (30 minutes)

Build script already configured to process all catalog files. No changes needed.

### Task 4: Test Compilation (30 minutes)

```bash
cargo clean -p simple_i18n
cargo build -p simple_i18n
cargo test -p simple_i18n
```

**Expected**: All catalogs compile successfully, tests pass.

---

## Phase 1C: SSpec Test Creation (NEW)

### Goal
Create comprehensive SSpec test files for all 84 new error codes.

### Test File Organization

```
test/features/errors/
├── parser/
│   ├── e0013_invalid_range_pattern.spl
│   ├── e0014_invalid_literal_pattern.spl
│   ├── e0015_unterminated_attribute.spl
│   └── e0016_expected_item.spl
├── semantic/
│   ├── e1019_duplicate_binding.spl
│   ├── e1020_argument_count_mismatch.spl
│   ├── ...
│   └── e1080_type_too_complex.spl
├── control_flow/
│   ├── e1104_return_in_closure.spl
│   └── e1105_invalid_control_flow.spl
├── capabilities/
│   ├── e1301_capability_violation.spl
│   └── e1302_isolation_violation.spl
├── macros/
│   └── e1403_keyword_in_macro.spl
└── ffi/
    └── e4005_type_not_ffi_safe.spl
```

### SSpec Test Template

```simple
# test/features/errors/semantic/e1020_argument_count_mismatch.spl
Feature: E1020 - Argument Count Mismatch

Background:
  Given I have the Simple compiler
  And I am using language "en"

Scenario: Too few arguments
  When I write:
    '''
    fn add(a: i32, b: i32) -> i32:
      a + b

    val result = add(5)  # Error: missing argument
    '''
  Then I should see error E1020: "function expects 2 argument(s), but 1 were provided"
  And the error should point to the function call

Scenario: Too many arguments
  When I write:
    '''
    fn greet(name: str):
      print("Hello, {name}!")

    greet("Alice", "Bob")  # Error: too many arguments
    '''
  Then I should see error E1020: "function expects 1 argument(s), but 2 were provided"

Scenario: Korean language
  Given I am using language "ko"
  When I write:
    '''
    fn multiply(x: i32, y: i32) -> i32:
      x * y

    multiply(3)
    '''
  Then I should see error E1020: "함수는 2개의 인수를 기대하지만 1개가 제공되었습니다"
```

### Task: Generate All SSpec Tests

**Estimated Effort**: 10-12 hours (84 tests × 8 minutes each)

**Approach**: Generate basic tests automatically, then enhance manually.

**Tool**: Create SSpec test generator script:

```bash
./tools/generate_sspec_tests.sh E1020 "Argument Count Mismatch"
```

Generates template with:
- Feature name
- Basic scenario
- Korean language scenario
- Placeholder test code

---

## Feature Requirements Analysis

### Features Needed for Full Error Support

| Feature | Priority | Effort | Errors Enabled |
|---------|----------|--------|----------------|
| **Module Privacy** | High | 2-3 weeks | E1038-E1040, E1046 |
| **Capability Enhancements** | High | 4-6 weeks | E1301-E1302 |
| **Associated Types** | High | 3-4 weeks | E1026-E1028 |
| **Closure Capture Analysis** | Medium | 2-3 weeks | E1036 |
| **Const Evaluation** | Medium | 3-4 weeks | E1024, E1060 |
| **Advanced Patterns** | Medium | 2-4 weeks | E1068, E1052 |
| **Exhaustiveness Checking** | Medium | 2-3 weeks | E0004 (future) |
| **Generators/Yield** | Low | 4-6 weeks | E1057 |

### Immediate Implementation (No New Features)

These errors can be implemented **immediately** without new features:

**Parser** (4): E0013-E0016
**Semantic** (30): E1019-E1024, E1032-E1035, E1037, E1039, E1041-E1051, E1053-E1056, E1059, E1061-E1065
**Control Flow** (2): E1104-E1105
**Macros** (1): E1403
**FFI** (1): E4005

**Total Immediate**: 38 error codes

### Deferred (Needs Features)

**Requires Module Privacy** (6): E1038-E1040, E1046
**Requires Capabilities** (2): E1301-E1302
**Requires Associated Types** (3): E1026-E1028
**Requires Closures** (1): E1036
**Requires Const Eval** (2): E1024, E1060
**Requires Patterns** (2): E1068, E1052
**Requires Generators** (1): E1057

**Total Deferred**: 17 error codes

**Can Implement Now**: E1024, E1060, E1068, E1052 (partial, simpler cases)

---

## Updated Implementation Timeline

### Phase 1B: Catalog Expansion (1 week)
- Days 1-2: Extend English catalogs (84 codes)
- Days 3-5: Create Korean translations (84 codes)
- Day 5: Test compilation, validate

### Phase 1C: SSpec Test Creation (2 weeks)
- Week 1: Create 40 SSpec tests (high-priority errors)
- Week 2: Create 44 SSpec tests (remaining errors)
- Throughout: Manual testing and refinement

### Phase 2: Compiler Integration (3-4 weeks)
- Week 1: Integrate immediate errors (38 codes)
- Week 2-3: Implement features (module privacy, const eval)
- Week 4: Integrate deferred errors

### Phase 3-6: Original Plan
- Phase 3: Runtime integration (2-3 hours)
- Phase 4: Panic messages (1-2 hours)
- Phase 5: Testing & validation (2-3 hours)
- Phase 6: Documentation (1-2 hours)

**Total Estimated Time**: 6-7 weeks

---

## Success Criteria

### Phase 1B Success

- [ ] All 84 new error codes added to catalogs
- [ ] All 84 codes translated to Korean
- [ ] Build succeeds with all catalogs
- [ ] No duplicate error code numbers
- [ ] Consistent message format

### Phase 1C Success

- [ ] All 84 SSpec tests created
- [ ] Tests cover positive and negative cases
- [ ] Korean language variants included
- [ ] Tests pass (or properly marked as pending)
- [ ] Documentation in test files

### Overall Success (After Phase 2)

- [ ] 164 total error codes
- [ ] 100% Korean translation
- [ ] ~38 codes integrated in compiler
- [ ] ~17 codes marked as needing features
- [ ] ~29 codes implemented after features complete
- [ ] Comprehensive SSpec test suite
- [ ] Feature roadmap documented

---

## Next Steps

**Immediate** (This Week):
1. Start Phase 1B: Extend catalog files
2. Create Korean translations
3. Test compilation

**Following Week**:
1. Start Phase 1C: Generate SSpec test templates
2. Begin creating comprehensive tests
3. Document test patterns

**Month 1**:
1. Complete all SSpec tests
2. Begin Phase 2 compiler integration
3. Implement module privacy feature

**Month 2-3**:
1. Implement capability enhancements
2. Implement associated types
3. Complete compiler integration

---

## Summary

**Current**: 80 error codes
**After Phase 1B**: 164 error codes (+84)
**Coverage**: ~32% of Rust's error space
**Effort**: 6-7 weeks total

This expansion brings Simple's error system to a professional, comprehensive state while maintaining focus on applicable errors and Simple's design philosophy.

---

**Document Status**: Planning Complete
**Next Document**: SSpec test suite generation plan
