# Simple BDD Spec Framework - Guide

A Ruby/RSpec-style testing DSL for behavior-driven tests.

## Contents

1. [Quick Start](#quick-start)
2. [Core Concepts](#core-concepts)
3. [Context Sharing](#context-sharing)
4. [BDD Pattern](#bdd-given-when-then-pattern)
5. [Test Organization](#test-organization)
6. [Best Practices](#best-practices)
7. [Troubleshooting](#troubleshooting)

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

    context "subtraction":
        it "subtracts numbers":
            expect 10 - 3 == 7
```

Run tests:
```bash
simple test
```

---

## Core Concepts

### 1. Test Groups

**describe** - Top-level group:
```simple
describe "String":
    it "works":
        expect true
```

**context** - Nested group (alias for describe):
```simple
describe "Array":
    context "when empty":
        it "returns 0 length":
            expect [].len() == 0

    context "when populated":
        it "returns length":
            expect [1, 2, 3].len() == 3
```

### 2. Test Cases

```simple
it "description of behavior":
    expect actual == expected
```

### 3. Fixtures

**Unnamed eager setup** - Runs before each example:
```simple
context "setup":
    given:
        setup_database()
        load_fixtures()

    it "works with setup":
        expect true
```

**Lazy fixture** - Memoized once per example:
```simple
context "with user":
    given_lazy :user, \:
        { name: "Alice", id: 42 }

    it "accesses user":
        expect user.name == "Alice"

    it "same user in example":
        expect user.id == 42
```

**Named eager setup** - Documented setup step:
```simple
context "complex setup":
    given :db_connect, \:
        database.connect()

    given :load_schema, \:
        database.migrate()

    it "has both setups":
        expect true
```

**Plain variables** - Using let:
```simple
context "with values":
    let x = 10
    let y = 20

    it "calculates sum":
        expect x + y == 30
```

### 4. Hooks

```simple
context "with hooks":
    before_each:
        setup()

    after_each:
        cleanup()

    before_all:
        expensive_init()

    after_all:
        expensive_cleanup()

    it "example":
        expect true
```

### 5. Assertions

**Value assertions:**
```simple
expect value == expected
expect value != expected
expect value > other
expect value < other
```

**Matcher assertions:**
```simple
expect 5 to eq 5
expect 10 to gt 5
expect [1, 2] to include 1
expect "" to be_empty
expect nil to be_nil
```

**Negation:**
```simple
expect 5 not_to eq 6
expect 10 not_to lt 5
```

**Exception assertions:**
```simple
expect_raises ValueError:
    raise ValueError("error")

expect_raises:
    risky_operation()
```

---

## Context Sharing

Define reusable contexts once, use everywhere.

### Define

```simple
context_def :admin_user:
    given_lazy :user, \:
        { email: "admin@example.com", role: "admin" }

    given:
        authorize_admin()
```

### Reference

```simple
describe "AdminPanel":
    context :admin_user:
        it "admin can access":
            expect user.role == "admin"
```

### Compose Multiple

```simple
context_def :auth:
    given_lazy :token, \: "auth_xyz"

context_def :database:
    given:
        db.connect()

describe "API":
    context_compose :auth, :database:
        it "has both":
            expect true
```

### Sequential Setup

Combine context references with variable definitions:

```simple
context_def :users:
    given_lazy :admin, \:
        { id: 1, name: "Admin" }

context "test":
    given:
        given :users
        let admin_key = "admin_" + admin.id.to_string()
        let greeting = "Hi, " + admin.name

    it "uses all setup":
        expect admin_key == "admin_1"
        expect greeting == "Hi, Admin"
```

---

## BDD Given-When-Then Pattern

Structure tests as scenarios:

```simple
context_def :calculator_state:
    # Given: initial state
    given_lazy :calc, \:
        Calculator.new()

describe "Calculator":
    context :calculator_state:
        it "starts at zero":
            expect calc.value == 0

        context "when adding 5":
            # When: action
            given:
                calc.add(5)

            # Then: verify
            it "value is 5":
                expect calc.value == 5

        context "when multiplying by 2":
            # When: action
            given:
                calc.multiply(2)

            # Then: verify
            it "value is 0":
                expect calc.value == 0
```

Mapping:
- **Given** → `context_def` with `given_lazy`
- **When** → `given:` block
- **Then** → `it` block

---

## Test Organization

### File Structure

```
test/
  __init__.spl
  unit/
    feature_spec.spl
  integration/
    api_spec.spl
  system/
    workflow_spec.spl
```

### Naming Conventions

- Files: `feature_spec.spl`
- Describe: `describe "ClassName":`
- Context: `context "when condition":`
- Test: `it "does something":`

### Test Levels

**Unit** - Fast, isolated:
```simple
describe "Parser":
    it "parses tokens":
        expect Parser.parse("1 + 2") != nil
```

**Integration** - Module boundaries:
```simple
describe "Database":
    before_all:
        db.connect()

    it "queries work":
        expect db.query("SELECT 1") != nil
```

**System** - End-to-end:
```simple
describe "API Server":
    before_all:
        start_server()

    it "handles requests":
        expect api.get("/health").status == 200
```

---

## Best Practices

### Do

- Name clearly: `it "adds two positive numbers":` not `it "works":`
- One assertion concept per test
- Use context sharing for reusable fixtures
- Mark Given-When-Then with comments
- Use `given_lazy` for test data, `given:` for setup

### Don't

- Multiple behaviors per test
- Test implementation details
- Share mutable state between tests
- Use vague test names
- Skip without marking `pending`

---

## Common Patterns

### Setup Once, Use Multiple Times

```simple
context_def :api_client:
    given_lazy :client, \:
        APIClient.new()

describe "API":
    context :api_client:
        it "test 1":
            expect client != nil

        it "test 2":
            expect client != nil
```

### Test Data Variants

```simple
context_def :empty_list:
    given_lazy :items, \: []

context_def :filled_list:
    given_lazy :items, \: [1, 2, 3]

describe "List":
    context :empty_list:
        it "is empty":
            expect items.len() == 0

    context :filled_list:
        it "has items":
            expect items.len() == 3
```

### Composed Setup

```simple
context_def :database:
    given:
        db.connect()

context_def :fixtures:
    given:
        load_fixtures()

context_def :auth:
    given_lazy :token, \: "xyz"

describe "Integration":
    context_compose :database, :fixtures, :auth:
        it "full setup works":
            expect true
```

---

## Troubleshooting

### Fixture not available

**Problem:**
```simple
context "test":
    it "uses user":
        expect user.name == "Alice"  # Error: user undefined
```

**Solution:**
```simple
context "test":
    given_lazy :user, \:
        { name: "Alice" }

    it "uses user":
        expect user.name == "Alice"
```

### Context not found

**Problem:**
```simple
context :undefined_context:  # Error: not found
    it "fails":
        expect true
```

**Solution:**
```simple
context_def :my_context:
    given_lazy :value, \: 42

context :my_context:
    it "works":
        expect value == 42
```

### State leaking between tests

**Problem:**
```simple
context "test":
    let x = 0

    it "modifies x":
        x = 5
        expect x == 5

    it "should be fresh":
        expect x == 0  # Fails: x is still 5
```

**Solution:**
```simple
context "test":
    given:
        x = 0

    it "modifies x":
        x = 5
        expect x == 5

    it "is fresh":
        expect x == 0  # Passes: fresh setup
```

---

## See Also

- [BDD Specification](spec/bdd_spec.md)
- [Matchers Reference](spec_matchers_reference.md)
