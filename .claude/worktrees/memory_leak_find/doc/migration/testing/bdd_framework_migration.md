# Migrating to SSpec BDD Framework

**Date:** 2026-01-21
**Version:** 1.0
**Audience:** Simple developers migrating from doctest or external test frameworks

## Overview

This guide helps you migrate from doctest or external test frameworks to the SSpec BDD framework. SSpec provides a comprehensive testing solution with RSpec-style syntax, built-in coverage tracking, and multiple output formats.

## Quick Comparison

| Feature | Doctest | SSpec BDD |
|---------|---------|-----------|
| **Syntax** | Python-style comments | describe/context/it blocks |
| **Organization** | Inline with code | Separate test files |
| **Hooks** | None | before/after each/all |
| **Fixtures** | None | let, given, shared contexts |
| **Coverage** | Manual | Built-in tracking |
| **Formatters** | Basic | Progress, doc, JSON, HTML |
| **CI Integration** | Limited | Codecov, Coveralls support |

## Migration Strategies

### Strategy 1: Gradual Migration (Recommended)

1. Keep existing doctests
2. Add new tests using SSpec
3. Convert doctests incrementally
4. Both frameworks can coexist

### Strategy 2: Full Migration

1. Convert all tests at once
2. Remove doctest infrastructure
3. Use only SSpec going forward

## Converting Doctests to SSpec

### Before (Doctest):

```simple
fn add(a: i32, b: i32) -> i32:
    """
    Add two numbers.

    Example:
        >>> add(2, 3)
        5
        >>> add(-1, 1)
        0
    """
    return a + b
```

### After (SSpec):

```simple
# test/unit/math_spec.spl
import spec.{describe, it, expect}
import spec.matchers.{eq}
import math.{add}

describe "Math - add":
    it "adds positive numbers":
        expect(add(2, 3)).to eq(5)

    it "adds negative numbers":
        expect(add(-1, 1)).to eq(0)
```

## Test Organization

### Directory Structure

```
simple/
├── src/              # Source code
├── test/
│   ├── unit/         # Unit tests (branch coverage)
│   │   └── math_spec.spl
│   ├── integration/  # Integration tests (function coverage)
│   │   └── api_spec.spl
│   └── system/       # System tests (method coverage)
│       └── e2e_spec.spl
└── simple.test.toml  # Test configuration
```

### File Naming

- Unit tests: `{module}_spec.spl`
- Integration tests: `{feature}_spec.spl`
- System tests: `{scenario}_spec.spl`

## Common Patterns

### 1. Basic Assertions

**Doctest:**
```simple
>>> result = calculate(10)
>>> result == 42
True
```

**SSpec:**
```simple
it "calculates correctly":
    val result = calculate(10)
    expect(result).to eq(42)
```

### 2. Exception Testing

**Doctest:**
```simple
>>> divide(10, 0)
Traceback (most recent call last):
    ...
DivisionError: Cannot divide by zero
```

**SSpec:**
```simple
it "raises error on division by zero":
    expect_raises(DivisionError):
        divide(10, 0)
```

### 3. Setup/Teardown

**Doctest:**
```simple
# Manual setup in each example
>>> db = Database.new()
>>> db.connect()
>>> user = db.create_user("test")
>>> user.name
"test"
>>> db.close()
```

**SSpec:**
```simple
describe "Database":
    val db = Database.new()  # Eager setup before each test

    before_each:
        db.connect()

    after_each:
        db.close()

    it "creates users":
        val user = db.create_user("test")
        expect(user.name).to eq("test")
```

### 4. Shared Setup

**Doctest:**
```simple
# Copy-paste setup in every test
```

**SSpec:**
```simple
# Define once, use everywhere
context_def :admin_user:
    given_lazy :user, \: User.new("admin", role: "admin")

describe "Admin Features":
    context :admin_user:
        it "can delete users":
            expect(user.can_delete()).to be_true()
```

## Advanced Features

### 1. Lazy Evaluation

```simple
describe "Expensive Resource":
    # Only created if test uses it
    let_lazy :database, \: Database.connect("test_db")
    let_lazy :large_dataset, \: load_dataset("1GB_file.csv")

    it "uses database":
        database.query("SELECT 1")  # Database created here

    it "doesn't need database":
        expect(true).to be_true()  # Database NOT created
```

### 2. Shared Examples

```simple
shared_examples "a collection":
    it "supports size":
        expect(collection.size()).to gt(0)

    it "supports empty check":
        expect(collection.is_empty()).to be_false()

describe "Array":
    val collection = [1, 2, 3]
    it_behaves_like "a collection"

describe "List":
    val collection = List.from([1, 2, 3])
    it_behaves_like "a collection"
```

### 3. Tags and Filtering

```simple
describe "API":
    it "GET /users":
        pass.with_tag("integration").with_tag("api")

    slow_it "loads large dataset":
        # Skipped unless RUN_SLOW_TESTS=1
        load_dataset("huge.csv")
```

Run specific tests:
```bash
simple test --tag integration    # Only integration tests
simple test --tag api            # Only API tests
simple test --slow               # Include slow tests
simple test Calculator           # Tests matching "Calculator"
```

## Coverage Configuration

### simple.test.toml

```toml
[test]
unit_coverage = "branch"           # 90%+ branch coverage
integration_coverage = "function"  # 100% public function coverage
system_coverage = "method"         # 100% method coverage

unit_threshold = 90.0
integration_threshold = 100.0
system_threshold = 100.0
```

### Coverage Levels

| Test Type | Coverage Type | Threshold | Goal |
|-----------|---------------|-----------|------|
| Unit | Branch/Condition | 90% | Thorough logic testing |
| Integration | Public Functions | 100% | All APIs tested |
| System | Class/Struct Methods | 100% | All behaviors tested |

## Running Tests

### Basic Commands

```bash
# Run all tests
simple test

# Run with specific formatter
simple test --format doc
simple test --format json -o results.json

# Run specific test types
simple test --tag unit
simple test --tag integration
simple test --tag system

# Run with coverage
simple test --coverage
simple test --coverage --html coverage.html

# Run slow tests
simple test --slow

# Filter by pattern
simple test Calculator
simple test "addition"
```

### CI Integration

```yaml
# .github/workflows/test.yml
- name: Run Tests
  run: simple test --format json -o test-results.json

- name: Generate Coverage
  run: simple test --coverage --codecov coverage.json

- name: Upload to Codecov
  uses: codecov/codecov-action@v3
  with:
    files: ./coverage.json
```

## Best Practices

### 1. One Assertion Per Test

**Bad:**
```simple
it "does everything":
    expect(add(1, 1)).to eq(2)
    expect(subtract(5, 3)).to eq(2)
    expect(multiply(2, 3)).to eq(6)
```

**Good:**
```simple
it "adds numbers":
    expect(add(1, 1)).to eq(2)

it "subtracts numbers":
    expect(subtract(5, 3)).to eq(2)

it "multiplies numbers":
    expect(multiply(2, 3)).to eq(6)
```

### 2. Descriptive Test Names

**Bad:**
```simple
it "test 1":
    ...
```

**Good:**
```simple
it "adds positive integers correctly":
    ...
```

### 3. Use Contexts for Scenarios

```simple
describe "User":
    context "when admin":
        val user = User.new(role: "admin")

        it "can delete users":
            expect(user.can_delete()).to be_true()

    context "when regular user":
        val user = User.new(role: "user")

        it "cannot delete users":
            expect(user.can_delete()).to be_false()
```

### 4. Keep Tests Fast

- Use `let_lazy` for expensive resources
- Mock external services
- Use `slow_it` for tests >120s
- Run slow tests separately in CI

## Common Issues

### Issue 1: Tests Running Slow

**Solution:** Use lazy evaluation
```simple
# Before: Always created
val expensive = create_expensive_resource()

# After: Created only when used
let_lazy :expensive, \: create_expensive_resource()
```

### Issue 2: Shared State Between Tests

**Solution:** Use `before_each` to reset state
```simple
describe "Counter":
    var counter = Counter.new()

    before_each:
        counter = Counter.new()  # Fresh instance per test

    it "increments":
        counter.increment()
        expect(counter.value()).to eq(1)
```

### Issue 3: Complex Setup

**Solution:** Use context definitions
```simple
context_def :database_setup:
    given_lazy :db, \: Database.connect()
    given_lazy :admin, \: db.create_user("admin", admin: true)

describe "Feature":
    context :database_setup:
        it "works":
            admin.do_something()
```

## Migration Checklist

- [ ] Create `test/` directory structure
- [ ] Create `simple.test.toml` configuration
- [ ] Convert simple doctests first
- [ ] Add hooks for complex setup/teardown
- [ ] Use contexts for scenarios
- [ ] Tag tests appropriately
- [ ] Set up CI integration
- [ ] Generate coverage reports
- [ ] Document test patterns for team
- [ ] Remove old doctest infrastructure (optional)

## Getting Help

- **Documentation:** `doc/guide/sspec.md`
- **Examples:** `doc/examples/bdd_spec/`
- **Template:** `.claude/templates/sspec_template.spl`
- **Skill:** Run `/sspec` in Claude Code

## Next Steps

1. Start with a small module
2. Convert its doctests to SSpec
3. Run tests and verify coverage
4. Iterate on other modules
5. Share learnings with team

The SSpec framework provides a solid foundation for comprehensive testing in Simple. Take your time with the migration and leverage the framework's features to write better, more maintainable tests.
