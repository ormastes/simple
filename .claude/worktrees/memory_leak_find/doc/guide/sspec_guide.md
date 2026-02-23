# SSpec Guide - BDD Testing Framework

**Status:** Stable
**Feature IDs:** #302
**Keywords:** testing, bdd, rspec, describe, it, expect, sspec

SSpec is a BDD (Behavior-Driven Development) testing framework for the Simple language, inspired by RSpec. It combines executable tests written in Simple syntax with markdown documentation embedded as triple-quoted strings.

---

## Table of Contents

1. [Quick Start](#quick-start)
2. [File Structure](#file-structure)
3. [BDD DSL Syntax](#bdd-dsl-syntax)
4. [Matchers Reference](#matchers-reference)
5. [Hooks](#hooks)
6. [Fixtures & Setup](#fixtures--setup)
7. [Shared Examples](#shared-examples)
8. [Context Sharing](#context-sharing)
9. [Tags](#tags)
10. [Gherkin-Style Syntax](#gherkin-style-syntax)
11. [SSpec Format](#sspec-format)
12. [Writing Guidelines](#writing-guidelines)
13. [Runner & CLI](#runner--cli)
14. [Coverage Policy](#coverage-policy)
15. [Advanced Testing](#advanced-testing)
16. [Best Practices](#best-practices)
17. [Troubleshooting](#troubleshooting)

---

## Quick Start

```simple
import std.spec

describe "Calculator":
    context "addition":
        it "adds two numbers":
            expect 2 + 2 == 4

        it "adds negatives":
            expect 5 + (-3) == 2
```

Run tests:
```bash
simple test                           # Run all tests
simple test path/to/spec.spl          # Run specific test
simple test --tag slow                # Run tests with tag
```

---

## File Structure

### Naming Convention

Test files follow these patterns:
- `*_spec.spl` - BDD spec files (preferred)
- `*_test.spl` - Test files

### Directory Layout

```
test/
  unit/
    **/*_spec.spl          # Fast, isolated tests
  integration/
    **/*_spec.spl          # Module boundary tests
  system/
    **/*_spec.spl          # End-to-end tests
  feature/
    app/                   # CLI/tool system tests
    usage/                 # Language feature integration tests
```

### Test Pyramid

- **Unit** - Fast, isolated tests for internal behavior (private functions, pure logic)
- **Integration** - Validates public functions and module boundaries
- **System** - End-to-end flows with realistic environment

---

## BDD DSL Syntax

### describe

Creates a top-level example group:

```simple
describe "UserService":
    it "creates a user":
        val user = UserService.create("alice")
        expect(user.name).to_equal("alice")
```

### context

Creates nested groups for different scenarios:

```simple
describe "User":
    context "when logged in":
        it "shows dashboard":
            # test code

    context "when logged out":
        it "shows login form":
            # test code
```

### it

Defines a single test example:

```simple
describe "Array":
    it "returns length":
        expect([1, 2, 3].len()).to_equal(3)

    it "can be empty":
        expect([].is_empty()).to_equal(true)
```

### skip

Skip a test temporarily:

```simple
describe "Feature":
    skip "pending implementation":
        pass
```

### Expectations

**Value expectations:**
```simple
expect(actual).to_equal(expected)
expect(actual).to_be(expected)
expect(actual).to_be_nil()
expect(actual).to_contain(element)
expect(actual).to_start_with("prefix")
expect(actual).to_end_with("suffix")
expect(actual).to_be_greater_than(other)
expect(actual).to_be_less_than(other)
```

**Important:** Use built-in matchers only:
- `to_equal`, `to_be`, `to_be_nil`, `to_contain`
- `to_start_with`, `to_end_with`
- `to_be_greater_than`, `to_be_less_than`
- Use `to_equal(true)` not `to_be_true()`

---

## Matchers Reference

### Equality & Identity

```simple
expect(value).to_equal(expected)     # Equality
expect(obj).to_be(same_obj)          # Identity
expect(result).to_be_nil()           # Nil check
```

### Comparison

```simple
expect(5).to_be_greater_than(3)
expect(3).to_be_less_than(5)
```

### Collection

```simple
expect([1, 2, 3]).to_contain(2)
```

### String

```simple
expect("hello world").to_contain("world")
expect("hello").to_start_with("hel")
expect("hello").to_end_with("lo")
```

---

## Hooks

| Hook | Scope | Runs |
|------|-------|------|
| `before_each:` | per example | outer -> inner |
| `after_each:` | per example | inner -> outer |
| `before_all:` | per group | once, outer -> inner |
| `after_all:` | per group | once, inner -> outer |

```simple
describe "Database":
    before_each:
        setup_database()

    after_each:
        cleanup()

    it "inserts records":
        # test with db available
```

---

## Fixtures & Setup

### Lazy Fixtures

Memoized once per example:
```simple
context "with user":
    given_lazy :user, \:
        { name: "Alice", id: 42 }

    it "accesses user":
        expect user.name == "Alice"
```

### Named Eager Setup

```simple
context "complex setup":
    given :db_connect, \:
        database.connect()

    it "has setup":
        expect true
```

### Unnamed Eager Setup

```simple
context "setup":
    given:
        setup_database()

    it "works":
        expect true
```

---

## Shared Examples

Reuse test examples across multiple contexts:

```simple
shared_examples "a collection":
    it "has a length":
        expect(subject.len()).to_be_greater_than(0)

describe "Array":
    val subject = [1, 2, 3]
    it_behaves_like "a collection"
```

---

## Context Sharing

Define reusable setup groups:

```simple
context_def :as_admin:
    given_lazy :user, \:
        create(:user, :admin)

describe "AdminDashboard":
    context :as_admin:
        it "shows admin panel":
            expect page.has_selector(".admin-panel")

    context_compose :as_admin, :with_database:
        it "loads from database":
            expect user.data.is_persisted()
```

| Keyword | Purpose |
|---------|---------|
| `context_def :name:` | Define reusable context |
| `context :symbol:` | Reference context_def |
| `context_compose :a, :b:` | Compose multiple contexts |
| `given_lazy :name, \: ...` | Lazy fixture (memoized) |
| `given :name, \: ...` | Named eager fixture |
| `given:` | Unnamed eager setup |

---

## Tags

### Adding Tags

```simple
# @slow
# @integration

describe "SlowTest":
    it "takes time":
        sleep(1000)
```

Or with decorator:
```simple
#[tag("slow")]
describe "SlowTest":
    pass
```

### Running Tagged Tests

```bash
simple test --tag slow           # Run only @slow tests
simple test --tag integration    # Run only @integration tests
```

---

## Gherkin-Style Syntax

Simple supports Gherkin-style BDD for system tests:

```simple
examples addition:
    """Test data for addition"""
    a    b    result
    1    2    3
    10   20   30

feature Basic Calculator:
    scenario outline Adding two numbers:
        given fresh calculator:
        when add <a>:
        when add <b>:
        then value is <result>:
        examples addition:
```

### Keywords

| Form | Meaning |
|------|---------|
| `examples name:` | Named examples table |
| `feature name:` | Feature grouping |
| `scenario name:` | Single test case |
| `scenario outline name:` | Parameterized test |
| `given/when/then/and_then` | Step references |

---

## SSpec Format

### Triple-Quote Documentation

Embed markdown documentation in test files:

```simple
"""
# Feature Name Specification

**Status:** Stable
**Feature IDs:** #XXX-YYY
**Category:** Language

## Overview
Brief description of the feature.

## Specification
Detailed specification text.
"""

describe "Feature":
    it "basic behavior":
        expect true
```

### Generated Documentation

The `simple sspec-docgen` command extracts `"""..."""` blocks and generates markdown documentation in `doc/spec/`.

### Advantages Over Cucumber

| Aspect | Cucumber (.feature) | SSpec (.spl) |
|--------|---------------------|--------------|
| Language | Gherkin DSL | Native Simple |
| Type checking | No | Yes |
| IDE support | Limited | Full Simple tooling |
| Code reuse | Separate step definitions | Direct code |
| Documentation | Separate | Integrated |

---

## Writing Guidelines

### Spec File Structure

```simple
"""
# Feature Name

**Status:** Stable
**Feature IDs:** #XXX
**Keywords:** keyword1, keyword2
**Category:** Language

## Overview
Brief description.
"""

describe "Feature":
    context "basic usage":
        it "does something":
            expect true

    context "edge cases":
        it "handles boundary":
            expect true
```

### Status Values

- `Stable` - Complete spec + implementation
- `Implementing` - Complete spec, partial implementation
- `Draft` - Spec under development
- `Planned` - Not yet started

### Test Categories

1. **Syntax Tests** - Verify code compiles
2. **Behavior Tests** - Verify runtime behavior
3. **Error Tests** - Verify errors are caught
4. **Edge Case Tests** - Test boundaries

### Naming Conventions

Use descriptive names:
- `it "returns empty array when no users exist"`
- `it "adds two positive numbers"`

### Checklist for New Specs

- Header with Status, Feature IDs, Category
- Overview section
- At least 3-5 test cases (basic, common, edge, error)
- Descriptive test names
- File compiles without errors

---

## Runner & CLI

### Discovery

Default pattern: `test/**/*_spec.spl`

### Layer Selection

```bash
simple test --unit          # test/unit/
simple test --integration   # test/integration/
simple test --system        # test/system/
simple test --all           # entire test/
```

### Filtering

```bash
simple test --tag slow
simple test --fail-fast
simple test --seed 12345
```

### Output Formats

```bash
simple test --format text   # Default colored output
simple test --format json   # JSON output
simple test --format doc    # Documentation format
```

### Exit Codes

| Code | Meaning |
|------|---------|
| 0 | All pass |
| 1 | Test failures |
| 2 | Environment failure |
| 3 | Invalid config |

---

## Coverage Policy

| Layer | Metric | Target |
|-------|--------|--------|
| Integration | Public function touch | 100% |
| System | Public type touch | 100% |

Exceptions: `@no_system_test_required`, `@experimental`

---

## Advanced Testing

Four additional test layers (opt-in):

| Layer | Flag | Purpose |
|-------|------|---------|
| Fuzz | `--fuzz` | Random input crash testing |
| Resilience | `--chaos` | Resource failure recovery |
| Deployment | `--deploy` | Fresh install validation |
| Security | `--security` | Sandbox escape detection |

All are off by default for fast development cycles.

---

## Best Practices

### Do

- One assertion concept per test
- Use descriptive names
- Use context for related test groups
- Use `given_lazy` for test data
- Tag appropriately (`@slow`, `@integration`)
- Clean up with `after_each`

### Don't

- Multiple behaviors per test
- Test implementation details
- Share mutable state between tests
- Use vague test names
- Skip without marking `pending`

---

## Troubleshooting

### Fixture not available

```simple
# Wrong:
it "uses user":
    expect user.name == "Alice"  # Error: undefined

# Right:
given_lazy :user, \:
    { name: "Alice" }
it "uses user":
    expect user.name == "Alice"
```

### State leaking between tests

Use `given:` blocks to reset state before each test instead of `let` at context level.

---

## See Also

- [Feature Documentation](../feature/feature.md)
- [Test Guides](test.md)
- [Syntax Quick Reference](syntax_quick_reference.md)
