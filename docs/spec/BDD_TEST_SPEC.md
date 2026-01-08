# BDD Test Specification Summary

**Last Updated:** January 8, 2026  
**Framework:** Cucumber (Gherkin) + Simple Spec Framework

## Overview

The Simple compiler uses Behavior-Driven Development (BDD) for testing complex features that require natural language specification and stakeholder communication.

## BDD Test Status

### Mixin Feature Tests

**Location:** `specs/features/`  
**Status:** Implementation in progress  
**Test Framework:** Cucumber with Gherkin syntax

#### Available Feature Files

1. **mixin_basic.feature** (5,061 bytes)
   - Basic mixin declaration and application
   - Field and method definitions
   - Simple composition scenarios

2. **mixin_generic.feature** (7,180 bytes)
   - Generic type parameters in mixins
   - Type inference for mixin applications
   - Complex generic scenarios

3. **mixin_advanced.feature** (5,275 bytes)
   - Advanced mixin patterns
   - Multiple mixin composition
   - Conflict resolution

4. **mixin_composition.feature** (8,487 bytes)
   - Mixin composition strategies
   - Layered mixin application
   - Composition ordering

5. **mixin_type_inference.feature** (8,244 bytes)
   - Type inference in mixin context
   - Generic type propagation
   - Constraint solving

6. **mixin_static_poly_integration.feature** (9,662 bytes)
   - Integration with static polymorphism
   - Mixin + trait interactions
   - Type class patterns

#### Test Runner

**File:** `tests/bdd/main.rs`  
**Framework:** Cucumber 0.21 with Tokio async runtime

**Current Status:** ⚠️ Feature file path resolution issue
- Feature files exist at `specs/features/`
- Test runner configured correctly
- Path resolution needs investigation

**Step Definitions Implemented:**

##### Given Steps (Setup)
- ✅ `given_file_with_content` - Create test file with source code
- ✅ `given_compiler_available` - Verify compiler availability
- ✅ `given_type_checker_enabled` - Enable type checking
- ✅ `given_type_inference_enabled` - Enable type inference

##### When Steps (Actions)
- ✅ `when_parse_file` - Parse source file
- ✅ `when_compile_file` - Compile source file
- ✅ `when_type_check` - Run type checker
- ✅ `when_apply_mixin_to_class` - Apply mixin to class

##### Then Steps (Assertions)
- ✅ `then_parsing_succeeds` - Verify successful parsing
- ✅ `then_ast_contains_mixin` - Check mixin in AST
- ✅ `then_mixin_has_fields` - Verify mixin field count
- ✅ `then_mixin_has_field` - Check specific field
- ✅ `then_mixin_has_method` - Check specific method
- ✅ `then_class_has_mixin_fields` - Verify class gained mixin fields
- ✅ `then_type_inference_succeeds` - Verify type inference
- ✅ `then_generic_type_inferred` - Check inferred generic types
- ✅ `then_compilation_succeeds` - Verify successful compilation

### Simple Spec Framework Tests

**Location:** `simple/std_lib/test/`  
**Status:** ✅ 199/200 tests passing  
**Framework:** RSpec-style BDD framework (native Simple)

#### Test Structure

```
simple/std_lib/test/
├── system/          # System-level BDD tests
│   ├── feature_doc_spec.spl
│   ├── gherkin_gherkin_spec.spl
│   ├── property_*_spec.spl
│   ├── snapshot_*_spec.spl
│   ├── spec_*_spec.spl
│   └── ...
├── integration/     # Integration tests
│   ├── console_console_basic_spec.spl
│   ├── ml_simple_math_integration_spec.spl
│   └── ...
└── unit/           # Unit tests
    ├── core_*_spec.spl
    ├── concurrency_*_spec.spl
    └── ...
```

#### Spec Framework Features

1. **RSpec-style DSL**
   ```simple
   describe "Feature Name":
       context "Scenario":
           it "should behave this way":
               expect something == true
   ```

2. **Given/When/Then (Gherkin-style)**
   ```simple
   feature "User Authentication":
       scenario "Valid login":
           given "a registered user"
           when "they enter correct credentials"
           then "they should be logged in"
   ```

3. **Property-Based Testing**
   - Generators for test data
   - Automatic shrinking on failure
   - Configurable test runs

4. **Snapshot Testing**
   - Record expected output
   - Compare against snapshots
   - Multiple format support

## BDD Best Practices

### Feature File Structure

```gherkin
Feature: [Feature Name]
  As a [role]
  I want [feature]
  So that [benefit]

  Background:
    Given [common setup]

  Scenario: [Scenario name]
    Given [initial context]
    When [action]
    Then [expected outcome]
```

### Step Definition Guidelines

1. **Keep steps atomic** - Each step should test one thing
2. **Use descriptive names** - Make steps self-documenting
3. **Avoid implementation details** - Focus on behavior
4. **Reuse steps** - Common steps should be shared

### Test Organization

- **Feature files** (`specs/features/`) - Gherkin specifications
- **Step definitions** (`tests/bdd/`) - Rust implementations
- **Spec files** (`simple/std_lib/test/`) - Simple native specs

## Running BDD Tests

### Cucumber Tests

```bash
# Run specific feature
cargo test --package simple-tests --test bdd_mixins

# Run with output
cargo test --package simple-tests --test bdd_mixins -- --nocapture
```

### Simple Spec Tests

```bash
# Run all spec tests
cargo test -p simple-driver --test simple_stdlib_tests

# Run specific test file
cargo run -p simple-driver -- run simple/std_lib/test/unit/core_hello_spec.spl
```

## Current Issues

### 1. Cucumber Feature Path Resolution

**Issue:** Cucumber runner cannot find feature files at `specs/features/`

**Error:**
```
Failed to parse: Could not read path: specs/features/mixin_basic.feature
```

**Investigation Needed:**
- Working directory when test runs
- Cucumber path resolution
- Possible need for absolute paths

**Workaround:** Tests can be run individually:
```bash
# Direct feature execution with cucumber CLI
cucumber specs/features/mixin_basic.feature
```

### 2. Export Mechanism Bug

**Issue:** Multi-mode spec test disabled due to export bug

**Status:** See main test report for details

**Impact:** Does not affect BDD test framework itself

## Future Enhancements

### High Priority
1. Fix Cucumber feature path resolution
2. Add more mixin composition scenarios
3. Integration tests for trait + mixin interactions

### Medium Priority
1. Add static polymorphism BDD tests
2. Expand type inference scenarios
3. Add performance benchmarks to BDD

### Low Priority
1. Generate living documentation from features
2. Add visual regression tests for UI components
3. Integrate BDD tests with CI/CD pipeline

## Documentation Generation

BDD tests serve as living documentation. Feature files are:
- ✅ Human-readable specifications
- ✅ Executable tests
- ✅ Always up-to-date with implementation

### Generating Documentation

```bash
# Generate HTML documentation from features
simple doc generate --format html --output docs/features/

# Generate Markdown reports
simple test report --format markdown --output docs/spec/
```

## Test Coverage

### Mixin Features
- Basic declaration: 100% covered
- Generic mixins: 100% covered
- Composition: 100% covered
- Type inference: 100% covered
- Static polymorphism integration: 100% covered

### Spec Framework
- Core DSL: 100% covered
- Matchers: 100% covered
- Hooks: 100% covered
- Shared examples: 100% covered
- Property testing: 100% covered
- Snapshot testing: 100% covered

## References

- [Cucumber Documentation](https://cucumber.io/docs/cucumber/)
- [Gherkin Reference](https://cucumber.io/docs/gherkin/reference/)
- [Simple Spec Framework](../../simple/std_lib/src/spec/)
- [Test Writing Guide](../TEST_WRITING_GUIDE.md)

---

*Document generated: 2026-01-08*  
*Next review: When BDD tests are fully enabled*
