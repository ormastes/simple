# Testing Framework

*Source: `simple/std_lib/test/features/infrastructure/testing_framework_spec.spl`*

---

# Testing Framework

**Feature ID:** #108
**Category:** Infrastructure - Testing
**Difficulty:** 3/5
**Status:** Complete

## Overview

The Testing Framework provides comprehensive test infrastructure including doctest
extraction from documentation, BDD-style SimpleTest syntax, coverage reporting,
and code duplication detection.

## Key Features

- **Doctest:** Extract and run tests from documentation
- **SimpleTest/SSpec:** BDD syntax (describe/it)
- **Async Tests:** Async function testing support
- **Coverage Reporting:** Line and branch coverage
- **Duplication Detection:** Find duplicated code blocks

## Implementation

**Primary Files:**
- `src/driver/src/doctest.rs` - Doctest extraction
- `src/driver/src/simple_test.rs` - SimpleTest BDD framework

**Testing:**
- `src/driver/tests/doctest_tests.rs` - Doctest test suite

## Test Coverage

Validates test framework features.

**Given** documentation with code examples
        **When** running doctest
        **Then** executes embedded tests

        **Example:**
        ```simple
        # Documentation:
        # Example:
        #     val x = 42
        #     expect(x).to(eq(42))
        ```

        **Verification:** Doctest extraction works

**Given** BDD test syntax
        **When** running tests
        **Then** executes test cases

        **Example:**
        ```simple
        describe "Feature":
            it "does something":
                expect(true).to(be_true())
        ```

        **Verification:** BDD syntax works

**Given** async test function
        **When** running test suite
        **Then** awaits completion

        **Verification:** Async tests work

**Given** executed tests
        **When** generating coverage report
        **Then** shows covered lines

        **Verification:** Coverage tracking works
