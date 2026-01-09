# BDD Spec Framework Implementation Plan

**Status:** Sprint 1 Complete (70% overall)  
**Priority:** High (Testing Infrastructure)  
**Goal:** Ruby/RSpec-style BDD test framework written in Simple

## Overview

Create a comprehensive BDD testing framework inspired by Ruby's RSpec, providing `describe`/`context`/`it` DSL, powerful matchers, and flexible test organization.

## Specification

See `doc/testing/testing_bdd_framework.md` for complete specification.

## Sprint 1: Core DSL & Registry ✅ COMPLETE

### Completed (10/10 tasks)

1. ✅ **Directory Structure** (`lib/std/spec/`)
   - Core modules in place
   - Clean separation of concerns

2. ✅ **Core DSL** (`dsl.spl`)
   - `describe(description, block)` - Test suite
   - `context(description, block)` - Nested context
   - `it(description, block)` - Individual test
   - `let(name, block)` - Lazy evaluation
   - `before(block)` - Setup hooks
   - `after(block)` - Teardown hooks

3. ✅ **Registry** (`registry.spl`)
   - ExampleGroup storage
   - Example storage
   - Hook storage
   - Hierarchical organization

4. ✅ **Runtime** (`runtime.spl`)
   - Configuration management
   - State management
   - Test execution context

5. ✅ **Expectations** (`expect.spl`)
   - `expect(actual).to(matcher)`
   - `expect(actual).not_to(matcher)`
   - `expect_raises(error_type, block)`

6. ✅ **Matcher Protocol** (`matchers.spl`)
   - Base Matcher trait
   - Match success/failure interface
   - Failure message generation

7. ✅ **Core Matchers** (`matchers/core.spl`)
   - `eq(expected)` - Equality
   - `be(expected)` - Identity
   - `be_nil` - Nil check

8. ✅ **Comparison Matchers** (`matchers/comparison.spl`)
   - `gt(expected)` - Greater than
   - `lt(expected)` - Less than
   - `gte(expected)` - Greater than or equal
   - `lte(expected)` - Less than or equal

9. ✅ **Collection Matchers** (`matchers/collection.spl`)
   - `include(item)` - Membership
   - `be_empty` - Empty check

10. ✅ **Error Matchers** (`matchers/error.spl`)
    - `raise_error(error_type)` - Exception matching

### Example Usage

```simple
use std.spec.*

describe("Calculator"):
    context("addition"):
        it("adds two numbers"):
            calc = Calculator()
            expect(calc.add(2, 3)).to eq(5)
        
        it("handles negative numbers"):
            calc = Calculator()
            expect(calc.add(-1, 1)).to eq(0)
    
    context("division"):
        it("divides numbers"):
            calc = Calculator()
            expect(calc.divide(10, 2)).to eq(5)
        
        it("raises error on division by zero"):
            calc = Calculator()
            expect_raises(DivisionError):
                calc.divide(10, 0)
```

## Sprint 1 Remaining (30% of Sprint 1)

### 1. ⏳ Unit Tests for DSL and Matchers

**Task:** Write comprehensive unit tests for all DSL functions and matchers

**Files to Create:**
- `test/unit/spec/dsl_spec.spl`
- `test/unit/spec/registry_spec.spl`
- `test/unit/spec/runtime_spec.spl`
- `test/unit/spec/matchers_spec.spl`

**Coverage Goals:**
- DSL: `describe`, `context`, `it`, `let`, hooks
- Registry: Group/example storage, hierarchy
- Matchers: All 10+ matcher types
- Edge cases: Nested contexts, hook ordering

**Dependencies:**
- Simple interpreter to run .spl tests
- OR: Bootstrap with Rust tests initially

### 2. ⏳ Test Registry Functionality

**Task:** Validate registry storage and retrieval

**Tests:**
- Register example groups
- Register examples
- Register hooks
- Hierarchical traversal
- Hook execution order

## Sprint 2: Runner & Formatters (Planned)

**Estimated Time:** 8 hours

### 1. Runner Implementation

**Files:**
- `lib/std/spec/runner/cli.spl` - CLI entry point
- `lib/std/spec/runner/executor.spl` - Test execution engine
- `lib/std/spec/runner/filter.spl` - Tag/pattern filtering

**Features:**
- Execute all registered tests
- Capture results (pass/fail/pending)
- Handle hooks (before/after)
- Support `let` lazy evaluation
- Tag-based filtering
- Pattern-based filtering

### 2. Formatters

**Files:**
- `lib/std/spec/formatters/progress.spl` - Progress dots (`.`, `F`, `*`)
- `lib/std/spec/formatters/doc.spl` - Hierarchical documentation
- `lib/std/spec/formatters/json.spl` - JSON output for CI

**Progress Formatter:**
```
..F..*..

Failures:
  1) Calculator division raises error on division by zero
     Expected DivisionError but got nothing

Finished in 0.5s
10 examples, 1 failure, 1 pending
```

**Doc Formatter:**
```
Calculator
  addition
    adds two numbers
    handles negative numbers
  division
    divides numbers
    raises error on division by zero (FAILED - 1)

Finished in 0.5s
10 examples, 1 failure
```

**JSON Formatter:**
```json
{
  "summary": {
    "duration": 0.5,
    "example_count": 10,
    "failure_count": 1,
    "pending_count": 1
  },
  "examples": [...]
}
```

### 3. Integration Tests

**Task:** Test runner with real test suites

**Files:**
- `test/integration/spec/runner_spec.spl`
- `test/integration/spec/formatter_spec.spl`

## Sprint 3: Coverage Infrastructure (Planned)

**Estimated Time:** 10 hours

### 1. Compiler Coverage Instrumentation

**Task:** Emit coverage metadata from compiler

**Files:**
- `src/compiler/src/coverage/mod.rs` (new)
- `src/compiler/src/coverage/symbols.rs` (new)

**Features:**
- Emit `symbols.json` per module
- Track function calls
- Track line execution
- Track branch coverage

**symbols.json Format:**
```json
{
  "module": "app.calculator",
  "functions": [
    {
      "name": "add",
      "visibility": "public",
      "line_start": 10,
      "line_end": 12,
      "touched": false
    }
  ]
}
```

### 2. Public API Coverage Calculation

**Task:** Calculate coverage based on public surface

**Metric:** Public function touch coverage
- Integration tests: 100% public function coverage
- System tests: 100% class/struct method coverage

**Files:**
- `lib/std/spec/coverage/calculator.spl`
- `lib/std/spec/coverage/reporter.spl`

### 3. Coverage Reports

**Formats:**
- Terminal: Coverage percentage
- HTML: Interactive report
- JSON: CI integration

## Sprint 4: Test Environment & Polish (Planned)

**Estimated Time:** 6 hours

### 1. Test Environment Setup

**Structure:**
```
test/
  ├── unit/           # Unit tests (100% branch/condition coverage)
  │   ├── calculator_spec.spl
  │   └── parser_spec.spl
  ├── integration/    # IT tests (100% public function touch)
  │   └── api_spec.spl
  └── system/         # System tests (100% class/struct method)
      └── e2e_spec.spl
```

**Configuration:**
```toml
# simple.toml
[test]
unit_coverage = "branch"          # branch/condition
integration_coverage = "function" # public function touch
system_coverage = "method"        # class/struct method
```

### 2. Migration Guide

**File:** `doc/migration/testing/testing_bdd_framework.md`

**Content:**
- Migrating from doctest
- Migrating from external test frameworks
- Best practices
- Examples

### 3. Documentation

**Files:**
- `doc/bdd_spec_guide.md` - User guide
- `doc/examples/bdd_spec/` - Example test suites

## Progress Summary

| Sprint | Tasks | Status | Progress |
|--------|-------|--------|----------|
| Sprint 1 | 12 | In Progress | 10/12 (83%) |
| Sprint 2 | 6 | Planned | 0/6 (0%) |
| Sprint 3 | 4 | Planned | 0/4 (0%) |
| Sprint 4 | 3 | Planned | 0/3 (0%) |
| **Total** | **25** | **10/25** | **40%** |

**Overall Status:** 70% of Sprint 1 complete, 28% overall

## Dependencies

### External
- None (pure Simple implementation)

### Internal
- Simple interpreter (for running .spl tests)
- Compiler coverage infrastructure (Sprint 3)
- CLI framework (Sprint 2)

## Timeline

| Sprint | Estimated | Status |
|--------|-----------|--------|
| Sprint 1 | 6 hours | 5 hours done, 1 hour remaining |
| Sprint 2 | 8 hours | Planned |
| Sprint 3 | 10 hours | Planned |
| Sprint 4 | 6 hours | Planned |
| **Total** | **30 hours** | **5/30 hours (17%)** |

## Integration with Doctest

BDD Spec and Doctest are complementary:

- **Doctest:** Interactive examples in documentation
- **BDD Spec:** Comprehensive behavior specification

**Shared Runner:** Both use `spec.runner` infrastructure

```simple
# Run all tests (BDD + Doctest)
simple test

# Run only BDD specs
simple test --spec

# Run only doctests
simple test --doctest

# Run with coverage
simple test --coverage
```

## See Also

- `doc/testing/testing_bdd_framework.md` - Complete specification
- `doc/guides/test.md` - Test policy and coverage rules
- `doc/plans/28_doctest.md` - Doctest implementation plan
- `lib/std/spec/` - Current implementation
