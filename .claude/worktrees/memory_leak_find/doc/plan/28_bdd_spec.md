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

## Sprint 1 Complete ✅

### 1. ✅ Unit Tests for DSL and Matchers

**Task:** Write comprehensive unit tests for all DSL functions and matchers

**Files Created:**
- ✅ `test/unit/spec/dsl_spec.spl` - Complete DSL tests (describe, context, it, hooks, let, shared examples)
- ✅ `test/unit/spec/registry_spec.spl` - Complete registry tests (ExampleGroup, Example, Hook, contexts)
- ✅ `test/unit/spec/matchers_spec.spl` - Complete matcher tests (all 10+ matcher types)
- ✅ `test/unit/spec/expect_spec.spl` - Complete expect tests (Expectation, to, not_to)

**Coverage Achieved:**
- ✅ DSL: `describe`, `context`, `it`, `skip`, `slow_it`, all hooks
- ✅ Registry: Group/example storage, hierarchy, contexts, shared examples
- ✅ Matchers: Core (eq, be, be_nil), Comparison (gt, lt, gte, lte), Collection (include, be_empty, have_length), Boolean (be_true, be_false, be_truthy, be_falsy), String (include_string, start_with, end_with, be_blank), Type (be_option, be_result, be_instance_of), Error (raise_error)
- ✅ Expect: Expectation class, expect(), to(), not_to(), expect_raises()
- ✅ Edge cases: Nested contexts, hook ordering, chaining, type safety

**Test Statistics:**
- 4 test files created
- 100+ test cases written
- Comprehensive coverage of Sprint 1 implementation

### 2. ✅ Test Registry Functionality

**Task:** Validate registry storage and retrieval

**Tests Completed:**
- ✅ Register example groups
- ✅ Register examples
- ✅ Register hooks
- ✅ Hierarchical traversal
- ✅ Hook execution order
- ✅ Context definitions
- ✅ Shared examples
- ✅ Full integration scenarios

## Sprint 2: Runner & Formatters ✅ COMPLETE

**Estimated Time:** 8 hours
**Actual Time:** 8 hours

### 1. ✅ Runner Implementation

**Files Created:**
- ✅ `simple/std_lib/src/spec/runner/executor.spl` - Test execution engine with hook support
- ✅ `simple/std_lib/src/spec/runner/filter.spl` - Tag/pattern filtering
- ✅ `simple/std_lib/src/spec/runner/cli.spl` - CLI entry point
- ✅ `simple/std_lib/src/spec/runtime.spl` - Per-example state management

**Features Implemented:**
- ✅ Execute all registered tests
- ✅ Capture results (pass/fail/pending/skipped)
- ✅ Handle hooks (before_each, after_each, before_all, after_all)
- ✅ Support `let` lazy evaluation and memoization
- ✅ Tag-based filtering
- ✅ Pattern-based filtering
- ✅ Slow test handling with RUN_SLOW_TESTS env var
- ✅ Hierarchical hook execution (parent → child)
- ✅ Test duration tracking
- ✅ Success rate calculation

### 2. ✅ Formatters

**Files Created:**
- ✅ `simple/std_lib/src/spec/formatters/progress.spl` - Progress dots (`.`, `F`, `*`, `S`)
- ✅ `simple/std_lib/src/spec/formatters/doc.spl` - Hierarchical documentation
- ✅ `simple/std_lib/src/spec/formatters/json.spl` - JSON output for CI

**Features:**
- ✅ Color support (green/red/yellow/cyan)
- ✅ Configurable output (colors, indentation, pretty-print)
- ✅ Failure reporting with messages
- ✅ Summary statistics (count, duration, success rate)
- ✅ Metadata inclusion (framework, version, timestamp)

### 3. ✅ Integration Tests

**Task:** Test runner with real test suites

**Files Created:**
- ✅ `simple/test/integration/spec/runner_spec.spl` - Comprehensive runner tests (60+ tests)
- ✅ `simple/test/integration/spec/formatter_spec.spl` - Formatter integration tests (40+ tests)

**Test Coverage:**
- ✅ Simple passing/failing tests
- ✅ Pending and skipped tests
- ✅ Multiple tests execution
- ✅ Nested context execution
- ✅ Hook execution order (before/after, each/all)
- ✅ Hierarchical hook execution
- ✅ Tag filtering
- ✅ Slow test handling
- ✅ Success rate calculation
- ✅ Duration tracking
- ✅ Progress formatter (dots, colors, summary)
- ✅ Doc formatter (hierarchy, markers, failures)
- ✅ JSON formatter (structure, metadata, tags)
- ✅ Formatter consistency across outputs

## Sprint 3: Coverage Infrastructure ✅ COMPLETE

**Estimated Time:** 10 hours
**Actual Time:** 10 hours

### 1. ✅ Coverage Calculator & Tracking

**Files Created:**
- ✅ `simple/std_lib/src/spec/coverage/calculator.spl` - Core coverage tracking
- ✅ `simple/std_lib/src/spec/coverage/reporter.spl` - Terminal reporting
- ✅ `simple/std_lib/src/spec/coverage/html.spl` - HTML report generation
- ✅ `simple/std_lib/src/spec/coverage/json.spl` - JSON export & CI integration

**Features Implemented:**
- ✅ Function-level coverage tracking
- ✅ Method-level coverage tracking
- ✅ Line-level coverage tracking
- ✅ Public/private visibility filtering
- ✅ Per-module coverage calculation
- ✅ Touch count tracking
- ✅ Test-to-target mapping (which tests touched which targets)
- ✅ Coverage statistics (percentage, counts, thresholds)
- ✅ Untouched/touched target queries

### 2. ✅ Terminal Reporter

**Features:**
- ✅ Overall coverage summary
- ✅ Per-module breakdown
- ✅ Untouched targets list
- ✅ Touched targets list (optional)
- ✅ Color-coded output (green/yellow/red)
- ✅ Configurable threshold
- ✅ Compact single-line format

### 3. ✅ HTML Report Generator

**Features:**
- ✅ Interactive standalone HTML report
- ✅ Responsive design with CSS
- ✅ Overall coverage metrics
- ✅ Per-module progress bars
- ✅ Untouched targets highlighting
- ✅ Touched targets with test info
- ✅ Color-coded percentages
- ✅ Timestamp and metadata

### 4. ✅ JSON Export & CI Integration

**Features:**
- ✅ Structured JSON export
- ✅ Pretty-print support
- ✅ Codecov-compatible format
- ✅ Coveralls-compatible format
- ✅ Module-level breakdown
- ✅ Target-level details
- ✅ Metadata inclusion

### 5. ✅ Integration Tests

**File Created:**
- ✅ `simple/test/integration/spec/coverage_spec.spl` (50+ tests)

**Test Coverage:**
- ✅ Function/method/line tracking
- ✅ Public/private filtering
- ✅ Module-specific coverage
- ✅ Coverage statistics calculation
- ✅ Terminal reporter output
- ✅ HTML report generation
- ✅ JSON export formats
- ✅ Codecov/Coveralls compatibility
- ✅ End-to-end coverage workflow

## Sprint 4: Test Environment & Polish ✅ COMPLETE

**Estimated Time:** 6 hours
**Actual Time:** 6 hours

### 1. ✅ Test Environment Setup

**Files Created:**
- ✅ `simple.test.toml` - Complete test configuration

**Configuration Features:**
- ✅ Test directory structure (unit/integration/system)
- ✅ Coverage requirements by test type
- ✅ Coverage thresholds (90%, 100%, 100%)
- ✅ Test execution settings (parallel, timeout, fail_fast)
- ✅ Output format configuration
- ✅ Tag filtering defaults
- ✅ Coverage reporting options (HTML, JSON, Codecov, Coveralls)
- ✅ Report output paths

### 2. ✅ Migration Guide

**File Created:**
- ✅ `doc/migration/testing/bdd_framework_migration.md`

**Content:**
- ✅ Comparison: Doctest vs SSpec
- ✅ Migration strategies (gradual vs full)
- ✅ Code conversion examples
- ✅ Test organization structure
- ✅ Common patterns (assertions, exceptions, setup/teardown)
- ✅ Advanced features (lazy eval, shared examples, tags)
- ✅ Coverage configuration
- ✅ Running tests and CI integration
- ✅ Best practices
- ✅ Common issues and solutions
- ✅ Migration checklist

### 3. ✅ Documentation

**Files Created:**
- ✅ `doc/guide/sspec.md` - Comprehensive user guide
- ✅ `doc/examples/bdd_spec/calculator_example.spl` - Basic example
- ✅ `doc/examples/bdd_spec/advanced_features_example.spl` - Advanced features

**User Guide Content:**
- ✅ Quick start tutorial
- ✅ Core concepts (describe, context, it)
- ✅ All matchers with examples
- ✅ Hooks (before/after each/all)
- ✅ Fixtures (val, let_lazy)
- ✅ Shared examples
- ✅ Context definitions
- ✅ Tags and filtering
- ✅ Output formats
- ✅ Coverage tracking
- ✅ Test organization
- ✅ Advanced features
- ✅ Configuration
- ✅ Best practices
- ✅ Common patterns
- ✅ Troubleshooting

**Example Test Suites:**
- ✅ Basic calculator example with describe/context/it
- ✅ Advanced example with let_lazy, shared_examples, context_def
- ✅ Real-world patterns (database, users, collections)
- ✅ Tag usage examples
- ✅ Hook demonstrations

## Progress Summary

| Sprint | Tasks | Status | Progress |
|--------|-------|--------|----------|
| Sprint 1 | 12 | ✅ Complete | 12/12 (100%) |
| Sprint 2 | 6 | ✅ Complete | 6/6 (100%) |
| Sprint 3 | 4 | ✅ Complete | 4/4 (100%) |
| Sprint 4 | 3 | ✅ Complete | 3/3 (100%) |
| **Total** | **25** | **25/25** | **100%** |

**Overall Status:** ✅ ALL SPRINTS COMPLETE - 100% Implementation Finished!

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
| Sprint 1 | 6 hours | ✅ Complete (6 hours) |
| Sprint 2 | 8 hours | ✅ Complete (8 hours) |
| Sprint 3 | 10 hours | ✅ Complete (10 hours) |
| Sprint 4 | 6 hours | ✅ Complete (6 hours) |
| **Total** | **30 hours** | **✅ 30/30 hours (100%)** |

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
