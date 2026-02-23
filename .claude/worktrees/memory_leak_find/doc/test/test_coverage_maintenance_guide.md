# Test Coverage Maintenance Guide
**Version:** 1.0
**Date:** 2026-02-03
**Status:** Active

---

## Overview

This guide provides procedures for maintaining and improving test coverage for the Simple language compiler, interpreter, and tooling.

---

## Test Organization

### Directory Structure

```
test/
├── compiler/                    # Compiler core tests
│   ├── resolve_spec.spl        # Method resolution (62 tests)
│   └── hir_lowering_spec.spl   # HIR lowering (37 tests)
├── lib/std/unit/compiler/
│   ├── loader/                  # Loader tests
│   │   ├── jit_instantiator_spec.spl    # JIT (16 tests)
│   │   └── module_loader_spec.spl       # Module loading (26 tests)
│   └── linker/                  # Linker tests
│       ├── smf_reader_spec.spl          # SMF reading (5 tests)
│       └── obj_taker_spec.spl           # Object taking (5 tests)
├── app/interpreter/
│   ├── core/
│   │   └── environment_spec.spl         # Environment (47 tests)
│   └── ast/
│       └── ast_convert_expr_spec.spl    # AST conversion (61 tests)
└── integration/
    └── compiler_interpreter_integration_spec.spl  # Integration (30 tests)
```

**Total:** 9 files, 289 tests (259 implemented, 30 integration stubs)

---

## Test Categories

### 1. Unit Tests (259 tests)
**Purpose:** Test individual functions and components in isolation

**Location:** `test/compiler/`, `test/lib/std/unit/`, `test/app/`

**Coverage Goal:** 80%+ of all functions

**Example:**
```simple
describe "TypeChecker Compatibility":
    it "matches identical int types":
        val checker = TypeChecker()
        val t1 = create_int_type(64, true)
        val t2 = create_int_type(64, true)

        expect(checker.is_compatible(t1, t2)).to(be_true())
```

### 2. Edge Case Tests (22 tests)
**Purpose:** Test boundary conditions, unusual inputs, error paths

**Location:** Embedded in unit test files (Test Groups 8-10+)

**Coverage Goal:** All error paths + boundary conditions

**Example:**
```simple
describe "TypeChecker Edge Cases - Nested Types":
    it "handles deeply nested optionals":
        val checker = TypeChecker()
        val base = create_int_type(32, true)
        val opt1 = create_optional_type(base)
        val opt2 = create_optional_type(opt1)
        val opt3 = create_optional_type(opt2)

        expect(checker.is_compatible(opt3, opt3)).to(be_true())
```

### 3. Integration Tests (30 stubs)
**Purpose:** Test complete pipeline end-to-end

**Location:** `test/integration/`

**Coverage Goal:** Major user workflows

**Status:** Stubs awaiting infrastructure

---

## Coverage Tracking

### Current Coverage (Phases 1-4)

| Component | File | Tests | Est. Coverage | Status |
|-----------|------|-------|---------------|--------|
| **Compiler** |
| Method Resolution | resolve.spl | 62 | 70% | ✅ Good |
| HIR Lowering | hir_lowering.spl | 37 | 40% | ⚠️ Partial |
| **Loader** |
| JIT Instantiator | jit_instantiator.spl | 16 | 60% | ⚠️ Partial |
| Module Loader | module_loader.spl | 26 | 25% | ⚠️ Stubs |
| SMF Reader | smf_reader.spl | 5 | 15% | ⚠️ Minimal |
| ObjTaker | obj_taker.spl | 5 | 10% | ⚠️ Minimal |
| **Interpreter** |
| Environment | environment.spl | 47 | 95% | ✅ Excellent |
| AST Conversion | ast_convert_expr.spl | 61 | 5% | ⚠️ Stubs |
| **Integration** |
| Full Pipeline | (various) | 30 | 0% | ⚠️ Stubs |

**Overall:** ~45% coverage across 4,616 LOC

---

## Adding New Tests

### Step 1: Identify Coverage Gap

Use the coverage analysis document:
```bash
# Review current coverage
cat doc/test/phase_1_3_coverage_analysis.md

# Identify untested functions
# Check "Gaps" sections for each component
```

### Step 2: Create Test File (if needed)

**Template:** `.claude/templates/sspec_template.spl`

```simple
"""
# Component Name Specification

**Feature IDs:** #XXXX-YYYY
**Category:** Compiler|Interpreter|Loader
**Difficulty:** 1-5/5
**Status:** In Progress

## Overview

Brief description of what this component does.

## Key Features

- Feature 1
- Feature 2
- Feature 3

## Implementation

File: `/path/to/implementation.spl`
"""

use std.test.sspec.*
use component.module.*

describe "Component Name":
    """
    ## Test Group Description

    What this group tests.
    """

    it "test description":
        # Arrange
        val input = create_test_input()

        # Act
        val result = function_under_test(input)

        # Assert
        expect(result).to(eq(expected))
```

### Step 3: Write Test Cases

**Pattern: AAA (Arrange, Act, Assert)**

```simple
it "descriptive test name":
    # Arrange - Set up test data
    val symbols = create_empty_symbol_table()
    val resolver = MethodResolver.new(symbols)

    # Act - Call the function
    val result = resolver.format_type(some_type)

    # Assert - Verify outcome
    expect(result).to(eq("expected format"))
```

### Step 4: Add Edge Cases

```simple
describe "Component Edge Cases":
    """
    ## Edge Case Testing

    Boundary conditions and unusual inputs.
    """

    it "handles empty input":
        expect(function(empty_value)).to(be_ok())

    it "handles very large input":
        val large = create_large_input(10000)
        expect(function(large)).to(not_crash())

    it "handles invalid input gracefully":
        val result = function(invalid_input)
        expect(result).to(be_err())
```

### Step 5: Verify Tests

```bash
# Parse check
simple test path/to/spec.spl --list

# Run tests (when implementation ready)
simple test path/to/spec.spl

# Check coverage (manual review)
# - Count tests vs functions
# - Review branch coverage by inspection
```

---

## Test Naming Conventions

### Describe Blocks
**Format:** Component or feature name
```simple
describe "TypeChecker Compatibility":
describe "Environment Variable Operations":
describe "ModuleLoader Integration":
```

### Context Blocks
**Format:** Scenario description with "when" or "for"
```simple
context "when checking primitive types":
context "when parsing valid header":
context "for nested generic types":
```

### Test Cases
**Format:** Behavior description starting with verb
```simple
it "matches identical int types":
it "rejects different int sizes":
it "handles deeply nested optionals":
it "returns error for invalid input":
```

---

## Coverage Goals by Component

### Critical Path (Target: 90%+)
- ✅ **Environment:** 95% (47 tests) - Excellent
- 🎯 **Type Checker:** 70% (24 tests) - Target: 90%
- 🎯 **Method Resolution:** 70% (62 tests) - Target: 90%

### Core Logic (Target: 70%+)
- ⚠️ **HIR Lowering:** 40% (37 tests) - Add expression lowering tests
- ⚠️ **JIT Instantiator:** 60% (16 tests) - Add FFI integration tests
- ⚠️ **Module Loader:** 25% (26 tests) - Implement stub tests

### Infrastructure (Target: 50%+)
- ⚠️ **SMF Reader:** 15% (5 tests) - Needs binary file fixtures
- ⚠️ **ObjTaker:** 10% (5 tests) - Needs FFI mocking
- ⚠️ **AST Conversion:** 5% (61 stubs) - Needs parser integration

### Integration (Target: 100% of workflows)
- ⚠️ **Full Pipeline:** 0% (30 stubs) - Awaiting infrastructure

---

## Test Infrastructure Needs

### Required for Current Stubs

**1. Parser Integration (61 tests blocked)**
- Tree-sitter integration
- Node/Tree construction helpers
- Sample parse trees

**Files Affected:**
- `test/app/interpreter/ast/ast_convert_expr_spec.spl`

**2. FFI Mocking (26 tests blocked)**
- Mock SMF file reader
- Mock JIT compiler
- Stub Rust functions

**Files Affected:**
- `test/lib/std/unit/compiler/linker/smf_reader_spec.spl`
- `test/lib/std/unit/compiler/linker/obj_taker_spec.spl`
- `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`

**3. Integration Infrastructure (30 tests blocked)**
- Complete compiler pipeline
- Runtime value system
- Module loader with SMF files
- GC instrumentation

**Files Affected:**
- `test/integration/compiler_interpreter_integration_spec.spl`

---

## Maintenance Procedures

### Monthly Review
1. Run all tests: `simple test`
2. Review pass rate: Target 95%+
3. Update coverage analysis
4. Identify new gaps from recent changes

### Per-Sprint
1. Add tests for new features (100% of new code)
2. Fix any broken tests immediately
3. Update documentation for test changes
4. Review and address flaky tests

### Per-Release
1. Ensure all critical paths have 90%+ coverage
2. Run integration tests if available
3. Update test organization docs
4. Archive old/obsolete tests

---

## Common Patterns

### Testing Result Types
```simple
it "returns Ok on success":
    val result = function_that_returns_result()

    match result:
        case Ok(value):
            expect(value).to(eq(expected))
        case Err(msg):
            fail("Expected Ok, got Err: {msg}")
```

### Testing Optional Types
```simple
it "returns Some for valid input":
    val result = function_that_returns_option()

    expect(result.?).to(be_true())
    expect(result.unwrap()).to(eq(expected))

it "returns nil for invalid input":
    val result = function_with_invalid_input()

    expect(result.?).to(be_false())
```

### Testing Errors
```simple
it "returns error for invalid input":
    val result = function_with_bad_input()

    match result:
        case Ok(_):
            fail("Expected Err, got Ok")
        case Err(msg):
            expect(msg).to(contain("expected error text"))
```

### Testing Side Effects
```simple
it "modifies state correctly":
    var state = create_initial_state()
    val before = state.value

    state.modify()

    expect(state.value).to_not(eq(before))
    expect(state.value).to(eq(expected_after))
```

---

## Troubleshooting

### Test Won't Parse
1. Check import statements: `use` not `import`
2. Verify syntax: `expect(x).to(eq(y))` not `expect(x) == y`
3. Check pattern matching: Use `case` not `when`
4. Validate helper functions: Must be defined before use

### Test Passes But Shouldn't
1. Check assertion: `expect(x).to(eq(y))` not `expect(x)`
2. Verify test logic: Arrange-Act-Assert pattern
3. Review mock data: Ensure realistic test fixtures
4. Check for false positives: Empty tests with `pass`

### Flaky Test
1. Identify non-deterministic code: Random, timing, I/O
2. Mock external dependencies: File system, network
3. Use fixed seeds: For randomness
4. Add retries: For timing-dependent tests

### Coverage Not Improving
1. Identify untested branches: Use manual code review
2. Add edge case tests: Boundary conditions
3. Test error paths: Invalid input, failures
4. Add integration tests: End-to-end workflows

---

## Resources

**Templates:**
- `.claude/templates/sspec_template.spl` - Test file template

**Documentation:**
- `doc/guide/sspec_complete_example.md` - SSpec framework guide
- `doc/test/phase_1_3_coverage_analysis.md` - Current coverage analysis
- `doc/test/test_db.sdn` - Test execution database

**Examples:**
- `test/compiler/resolve_spec.spl` - Comprehensive unit tests
- `test/app/interpreter/core/environment_spec.spl` - High coverage example
- `test/integration/compiler_interpreter_integration_spec.spl` - Integration test structure

**Commands:**
```bash
# Run all tests
simple test

# Run specific file
simple test path/to/spec.spl

# List tests without running
simple test --list

# Run with tags
simple test --tag=integration

# Run only slow tests
simple test --only-slow
```

---

## Future Improvements

### Short Term (1-2 sprints)
- [ ] Implement parser integration for AST conversion tests
- [ ] Create FFI mocking infrastructure
- [ ] Add error path tests for all components
- [ ] Increase HIR lowering coverage to 70%

### Medium Term (3-6 sprints)
- [ ] Build integration test infrastructure
- [ ] Implement all 30 integration tests
- [ ] Add performance benchmarks
- [ ] Create test fixture generators

### Long Term (6+ sprints)
- [ ] Automated coverage reporting
- [ ] Continuous integration
- [ ] Mutation testing
- [ ] Property-based testing framework

---

## Conclusion

**Current State:**
- ✅ Strong unit test foundation (259 tests)
- ✅ Excellent coverage for core utilities
- ✅ Clear documentation and organization

**Next Steps:**
- Implement FFI mocking for loader tests
- Add parser integration for AST tests
- Build integration test infrastructure
- Increase coverage for critical paths

**Maintenance:**
- Monthly coverage reviews
- Per-sprint test additions
- Per-release validation
- Continuous improvement

---

**Document Version:** 1.0
**Last Updated:** 2026-02-03
**Next Review:** 2026-03-03
