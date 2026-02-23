# SSpec BDD Framework - User Guide

**Version:** 1.0
**Date:** 2026-01-21

## Overview

SSpec is Simple's built-in BDD (Behavior-Driven Development) testing framework, inspired by Ruby's RSpec. It provides a clean, expressive DSL for writing tests with powerful features like hooks, fixtures, shared examples, and comprehensive coverage tracking.

## Quick Start

### 1. Write Your First Test

```simple
# test/unit/calculator_spec.spl
import spec.{describe, it, expect}
import spec.matchers.{eq}

describe "Calculator":
    it "adds two numbers":
        expect(2 + 3).to eq(5)
```

### 2. Run Tests

```bash
simple test
```

### 3. See Results

```
.

Finished in 0.01s
1 example, 0 failures
```

## Core Concepts

### describe - Test Suites

Group related tests together:

```simple
describe "User Authentication":
    it "allows login with valid credentials":
        ...

    it "rejects invalid password":
        ...
```

### context - Scenarios

Create different scenarios within a suite:

```simple
describe "Shopping Cart":
    context "when empty":
        it "shows zero items":
            ...

    context "with items":
        it "calculates total":
            ...
```

### it - Individual Tests

Define a single test case:

```simple
it "validates email format":
    expect(validate_email("test@example.com")).to be_true()
```

## Expectations and Matchers

### Basic Matchers

```simple
# Equality
expect(value).to eq(42)
expect(value).not_to eq(0)

# Identity
expect(obj).to be(same_obj)

# Nil/None
expect(None).to be_nil()
expect(Some(42)).not_to be_nil()
```

### Comparison Matchers

```simple
expect(10).to gt(5)      # greater than
expect(3).to lt(10)      # less than
expect(5).to gte(5)      # greater than or equal
expect(5).to lte(10)     # less than or equal
```

### Boolean Matchers

```simple
expect(true).to be_true()
expect(false).to be_false()

# For Option types
expect(Some(value)).to be_truthy()
expect(None).to be_falsy()
```

### Collection Matchers

```simple
expect([1, 2, 3]).to include(2)
expect([]).to be_empty()
expect([1, 2, 3]).to have_length(3)
expect([1, 2]).to have_size(2)
```

### String Matchers

```simple
expect("hello world").to include_string("world")
expect("hello").to start_with("hel")
expect("world").to end_with("rld")
expect("   ").to be_blank()
```

### Type Matchers

```simple
expect(Some(42)).to be_option()
expect(Ok(value)).to be_result()
expect(value).to be_a("String")
```

## Hooks - Setup and Teardown

### before_each / after_each

Run before/after every test:

```simple
describe "Database":
    var db: Database

    before_each:
        db = Database.connect()

    after_each:
        db.close()

    it "queries data":
        val result = db.query("SELECT 1")
        expect(result).not_to be_nil()
```

### before_all / after_all

Run once per test suite:

```simple
describe "Application":
    before_all:
        start_server()

    after_all:
        stop_server()

    it "responds to requests":
        ...
```

## Fixtures - Test Data

### val - Eager Fixtures

Evaluated before each test:

```simple
describe "User":
    val user = User.new("test")  # Created before each test

    it "has a name":
        expect(user.name).to eq("test")
```

### let_lazy - Lazy Fixtures

Evaluated only when accessed:

```simple
describe "Report":
    let_lazy :data, \: load_large_dataset()  # Only loaded if used

    it "processes data":
        expect(data.size()).to gt(0)  # Loaded here

    it "doesn't need data":
        expect(true).to be_true()  # NOT loaded
```

## Shared Examples

Define reusable test groups:

```simple
shared_examples "a collection":
    it "supports iteration":
        var count = 0
        for item in collection:
            count = count + 1
        expect(count).to gt(0)

describe "Array":
    val collection = [1, 2, 3]
    it_behaves_like "a collection"

describe "List":
    val collection = List.from([1, 2, 3])
    it_behaves_like "a collection"
```

## Context Definitions

Reusable setup contexts:

```simple
context_def :admin_user:
    given_lazy :user, \: User.new("admin", admin: true)
    given_lazy :token, \: auth.generate_token(user)

describe "Admin Panel":
    context :admin_user:
        it "allows access":
            expect(user.can_access_panel()).to be_true()

        it "has valid token":
            expect(token.is_valid()).to be_true()
```

## Tags and Filtering

### Adding Tags

```simple
it "fast test":
    pass.with_tag("unit").with_tag("fast")

it "slow test":
    pass.with_tag("integration").with_tag("slow")

slow_it "very slow test":
    # Automatically tagged with "slow"
    load_huge_dataset()
```

### Running Tagged Tests

```bash
# Run only unit tests
simple test --tag unit

# Exclude slow tests
simple test --exclude-tag slow

# Run slow tests
simple test --slow
```

## Output Formats

### Progress (Default)

```bash
simple test --format progress
```

Output:
```
..F..*..

Failures:
  1) Calculator divides by zero

Finished in 0.5s
8 examples, 1 failure, 1 pending
```

### Documentation

```bash
simple test --format doc
```

Output:
```
Calculator
  ✓ adds numbers
  ✓ subtracts numbers
  ✗ divides by zero (FAILED - 1)
  ○ multiplies complex numbers (PENDING)

Finished in 0.5s
4 examples, 1 failure, 1 pending
```

### JSON

```bash
simple test --format json -o results.json
```

Generates machine-readable JSON for CI/CD.

## Coverage Tracking

### Automatic Coverage

```bash
simple test --coverage
```

Shows:
```
Coverage Summary
================

Total Coverage: 85.00%
Touched: 17
Untouched: 3
Total Targets: 20

Untouched Targets
=================
  math::divide
  parser::parse_complex
  formatter::format_json
```

### HTML Report

```bash
simple test --coverage --html coverage.html
```

Generates interactive HTML coverage report.

### CI Integration

```bash
# Codecov
simple test --coverage --codecov coverage.json

# Coveralls
simple test --coverage --coveralls coverage.json
```

## Test Organization

### Directory Structure

```
test/
├── unit/              # Unit tests (branch coverage)
│   ├── math_spec.spl
│   └── parser_spec.spl
├── integration/       # Integration tests (function coverage)
│   └── api_spec.spl
└── system/           # System tests (method coverage)
    └── e2e_spec.spl
```

### Coverage Goals

| Type | Coverage | Threshold |
|------|----------|-----------|
| Unit | Branch/Condition | 90% |
| Integration | Public Functions | 100% |
| System | Class/Struct Methods | 100% |

## Advanced Features

### Pending Tests

```simple
skip "not yet implemented":
    # Will be marked as pending
    expect(feature_x()).to work()
```

### Slow Tests

```simple
slow_it "generates large report":
    # Skipped unless RUN_SLOW_TESTS=1
    generate_1000_page_report()
```

### Fail Fast

```bash
simple test --fail-fast  # Stop on first failure
```

### Verbose Output

```bash
simple test --verbose
```

## Configuration

### simple.test.toml

```toml
[test]
default_format = "progress"
parallel = true
fail_fast = false
timeout = 120

[coverage]
enabled = true
generate_html = true
public_only = true
```

## Best Practices

### 1. Use Descriptive Names

```simple
# Good
it "validates email format with RFC 5322 compliance":
    ...

# Bad
it "test 1":
    ...
```

### 2. One Concept Per Test

```simple
# Good
it "adds positive numbers":
    expect(add(2, 3)).to eq(5)

it "adds negative numbers":
    expect(add(-1, -1)).to eq(-2)

# Bad - multiple concepts
it "does math":
    expect(add(2, 3)).to eq(5)
    expect(subtract(5, 3)).to eq(2)
    expect(multiply(2, 3)).to eq(6)
```

### 3. Use Contexts for Scenarios

```simple
describe "User":
    context "when logged in":
        val user = User.new(logged_in: true)
        ...

    context "when logged out":
        val user = User.new(logged_in: false)
        ...
```

### 4. Keep Tests Fast

- Use `let_lazy` for expensive operations
- Mock external dependencies
- Use `slow_it` for long-running tests

### 5. Test Behavior, Not Implementation

```simple
# Good - tests behavior
it "sends welcome email":
    user.register()
    expect(email_sent_to(user.email)).to be_true()

# Bad - tests implementation
it "calls send_email method":
    expect(mailer).to have_received(:send_email)
```

## Common Patterns

### Testing Errors

```simple
it "raises error on invalid input":
    expect_raises(ValueError):
        parse("invalid")
```

### Testing State Changes

```simple
it "increments counter":
    val counter = Counter.new()
    val before = counter.value()
    counter.increment()
    expect(counter.value()).to eq(before + 1)
```

### Testing Collections

```simple
it "filters even numbers":
    val numbers = [1, 2, 3, 4, 5, 6]
    val evens = numbers.filter(\n: n % 2 == 0)
    expect(evens).to eq([2, 4, 6])
```

## Troubleshooting

### Tests Running Slow?

- Use `let_lazy` instead of `val`
- Mock expensive operations
- Check for N+1 queries
- Profile test execution

### Flaky Tests?

- Remove shared state
- Use `before_each` for fresh setup
- Avoid time-dependent assertions
- Fix race conditions

### Coverage Not 100%?

- Check untouched targets report
- Add missing test cases
- Verify test tags match configuration
- Review coverage thresholds

## Next Steps

- Read `/sspec` skill for quick reference
- Check `.claude/templates/sspec_template.spl` for template
- See `doc/examples/bdd_spec/` for examples
- Review `doc/migration/testing/bdd_framework_migration.md` for migration guide

Happy testing with SSpec!
