# Simple BDD Spec Framework - Complete Guide

The Simple BDD Spec Framework provides a Ruby/RSpec-style testing DSL for writing behavior-driven tests.

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

Run tests with:
```bash
simple test
```

## Core Concepts

### 1. Test Groups (describe/context)

**describe** - Top-level test group
```simple
describe "String":
    it "works":
        expect true
```

**context** - Nested test group (alias for describe)
```simple
describe "Array":
    context "when empty":
        it "returns 0 length":
            expect [].len == 0

    context "when populated":
        it "returns length":
            expect [1, 2, 3].len == 3
```

### 2. Test Cases (it)

Define individual test cases:
```simple
it "description of what it does":
    # test body
    expect actual == expected
```

Each `it` block is one test example.

### 3. Fixtures (given, given_lazy, let)

**Unnamed eager setup** - Runs before each example
```simple
context "setup":
    given:
        setup_database()
        load_fixtures()

    it "works with setup":
        expect true
```

**Named lazy fixture** - Memoized once per example
```simple
context "with user":
    given_lazy :user, \:
        { name: "Alice", id: 42 }

    it "accesses user":
        expect user.name == "Alice"

    it "same user in example":
        expect user.id == 42  # Memoized
```

**Named eager setup** - Documented setup step
```simple
context "complex setup":
    given :db_connect, \:
        database.connect()

    given :load_schema, \:
        database.migrate()

    it "has both setups":
        expect true
```

**Plain variables** - Using let
```simple
context "with values":
    let x = 10
    let y = 20

    it "calculates sum":
        expect x + y == 30
```

### 4. Hooks (before/after)

**before_each** - Runs before each example
```simple
context "with hooks":
    before_each:
        setup()

    it "example 1":
        expect true

    it "example 2":
        expect true  # Both examples run setup
```

**after_each** - Runs after each example
```simple
context "cleanup":
    after_each:
        cleanup()

    it "cleans up":
        expect true
```

**before_all** - Runs once before all examples in group
```simple
context "expensive setup":
    before_all:
        expensive_init()

    it "test 1":
        expect true

    it "test 2":
        expect true  # expensive_init runs only once
```

**after_all** - Runs once after all examples in group
```simple
context "cleanup":
    after_all:
        expensive_cleanup()

    it "test 1":
        expect true
```

### 5. Assertions (expect/expect_raises)

**Value assertions**
```simple
expect value == expected
expect value != expected
expect value > other
expect value < other
expect value.includes?(item)
```

**Matcher assertions**
```simple
expect 5 to eq 5
expect 10 to be_gt 5
expect [1, 2] to include 1
expect "" to be_empty
expect nil to be_nil
```

**Negation**
```simple
expect 5 not_to eq 6
expect 10 not_to be_lt 5
```

**Exception assertions**
```simple
expect_raises ValueError:
    raise ValueError("something went wrong")

expect_raises:
    risky_operation()
```

## Context Sharing (Advanced)

Define reusable contexts once, use them everywhere.

### Define a Context

```simple
context_def :admin_user:
    given_lazy :user, \:
        { email: "admin@example.com", role: "admin" }

    given:
        authorize_admin()
```

### Reference a Context

```simple
describe "AdminPanel":
    context :admin_user:
        it "admin can access":
            expect user.role == "admin"
```

### Compose Multiple Contexts

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

### Sequential Setup (Contexts + Variables)

Combine context references with variable definitions:

```simple
context_def :users:
    given_lazy :admin, \:
        { id: 1, name: "Admin" }

context "test":
    given:
        # Step 1: Reference context
        given :users

        # Step 2: Define derived variables
        let admin_key = "admin_" + admin.id.to_string()
        let greeting = "Hi, " + admin.name

    it "uses all setup":
        expect admin_key == "admin_1"
        expect greeting == "Hi, Admin"
```

### Reference Context Within Given Block

Apply a context's givens inline:

```simple
context_def :api_setup:
    given:
        start_server()

    given_lazy :client, \:
        API.new()

context "test":
    given:
        given :api_setup  # Apply all givens

        let request = {
            endpoint: "/api/test",
            client: client
        }

    it "has setup":
        expect true
```

## BDD Given-When-Then Pattern

Structure tests as Given-When-Then scenarios:

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
            # When: perform action
            given:
                calc.add(5)

            # Then: verify result
            it "value is 5":
                expect calc.value == 5

        context "when multiplying by 2":
            # When: perform action
            given:
                calc.multiply(2)

            # Then: verify result
            it "value is 0":
                expect calc.value == 0
```

Comments show BDD intent:
- **Given** - Context with `context_def` and `given_lazy`
- **When** - Action with `given:` block
- **Then** - Assertion with `it` block

## Test Organization

### File Structure

```
test/
  __init__.spl           # Shared imports (std.spec.*)
  unit/
    feature_spec.spl
    helper_spec.spl
  integration/
    api_spec.spl
  system/
    workflow_spec.spl
```

### Naming Conventions

- File names: `feature_spec.spl` or `feature_tests.spl`
- Describe blocks: `describe "ClassName":`
- Context blocks: `context "when condition":`
- Test cases: `it "should do something":`

### Test Levels

**Unit Tests** - Fast, isolated, no external dependencies
```simple
describe "Parser":
    it "parses tokens":
        expect Parser.parse("1 + 2") != nil
```

**Integration Tests** - Test module boundaries, limited external deps
```simple
describe "Database":
    context "with connection":
        before_all:
            db.connect()

        it "queries work":
            expect db.query("SELECT 1") != nil
```

**System Tests** - Full end-to-end, realistic environment
```simple
describe "API Server":
    context "with server running":
        before_all:
            start_server()

        it "handles requests":
            expect api.get("/health").status == 200
```

## Best Practices

### ✅ Do

- **Name clearly**: `it "adds two positive numbers":` not `it "works":`
- **One assertion per concept**: Group related assertions together
- **Use context sharing**: Define fixtures once, reuse everywhere
- **Use BDD comments**: Mark Given-When-Then steps clearly
- **Keep tests focused**: One behavior per test
- **Use fixtures**: `given_lazy` for test data, `given:` for setup

### ❌ Don't

- **Multiple behaviors per test**: One assertion concept per test
- **Test implementation**: Test behavior, not internal details
- **Share state between tests**: Each test should be independent
- **Ignore test names**: Test names are documentation
- **Skip tests silently**: Use `skip` or `pending` if needed
- **Create tight couples**: Mock external dependencies

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

        it "test 3":
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
            expect items.len == 0

    context :filled_list:
        it "has items":
            expect items.len == 3
```

### Composed Complex Setup

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

## Troubleshooting

### Fixture not available

**Problem**: Trying to use `user` but it's not defined
```simple
context "test":
    # Wrong - fixture not defined
    it "uses user":
        expect user.name == "Alice"
```

**Solution**: Define the fixture
```simple
context "test":
    given_lazy :user, \:
        { name: "Alice" }

    it "uses user":
        expect user.name == "Alice"
```

### Context not found

**Problem**: Referencing undefined context_def
```simple
context "test":
    context :undefined_context:
        it "fails":
            expect true
```

**Solution**: Define the context first
```simple
context_def :my_context:
    given_lazy :value, \: 42

context "test":
    context :my_context:
        it "works":
            expect value == 42
```

### Fresh setup not happening

**Problem**: State from one test leaks to next
```simple
context "test":
    let x = 0

    it "modifies x":
        x = 5
        expect x == 5

    it "should be fresh":
        expect x == 0  # Fails - x is still 5
```

**Solution**: Use fixtures or reset in before_each
```simple
context "test":
    given:
        x = 0

    it "modifies x":
        x = 5
        expect x == 5

    it "should be fresh":
        # Fresh setup before this test
        expect x == 0
```

## See Also

- [Context Sharing Usage Guide](doc/context_sharing_usage_guide.md)
- [BDD Specification](doc/spec/bdd_spec.md)
- [Matchers Reference](doc/spec_matchers.md) (if available)
