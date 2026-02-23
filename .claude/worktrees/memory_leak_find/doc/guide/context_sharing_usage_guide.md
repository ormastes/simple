# Context Sharing Usage Guide

A guide to using reusable Contexts with given fixtures in the Simple BDD spec framework.

## Overview

Context Sharing allows you to define reusable test setup (fixtures) once and use them across multiple test groups. This reduces duplication and improves test maintainability.

## Basic Syntax

### 1. Define a Reusable Context

```simple
context_def :context_name:
    given_lazy :fixture_name, \:
        # Return the fixture value (evaluated once per example)
        create_fixture()

    given:
        # Eager setup (runs before each example)
        setup_database()
```

**Key Points:**
- Use capital `C` for `Context` (different from lowercase `context`)
- Use `:` to mark the block start (consistent with Simple's if/while style)
- Use `given_lazy(:name)` for memoized fixtures
- Use `given { }` for eager setup blocks
- Contexts are registered globally

### 2. Reference a Single Context

```simple
context :context_name:
    it "uses the context":
        expect fixture_name == expected_value
```

**Key Points:**
- Use lowercase `context` with a Symbol (`:symbol_name`)
- All fixtures from the context are available
- Fixtures are memoized per example
- Each example gets fresh fixtures

### 3. Compose Multiple Contexts

```simple
context_compose :context1, :context2:
    it "has access to both contexts":
        expect fixture_from_context1 == value1
        expect fixture_from_context2 == value2
```

**Key Points:**
- Use `context_compose` with multiple Symbols
- Fixtures run in order (context1, then context2)
- All fixtures available in all examples

## Usage Patterns

### Pattern 1: Reusable Test Data

```simple
# Define the context
context_def :user_fixtures:
    given_lazy :admin_user, \:
        { name: "Admin", role: "admin", permissions: ["read", "write", "delete"] }

    given_lazy :regular_user, \:
        { name: "User", role: "user", permissions: ["read"] }

# Use it in multiple places
describe "User Permissions":
    context :user_fixtures:
        it "admin has delete permission":
            expect admin_user.permissions.contains("delete")

        it "regular user has no delete":
            expect not regular_user.permissions.contains("delete")
```

### Pattern 2: Database/External Service Setup

```simple
context_def :with_database:
    # Eager given - setup runs before each test
    given:
        db.clear_tables()

    # Lazy given - connection is memoized
    given_lazy :connection, \:
        db.connect("test")

describe "Database Operations":
    context :with_database:
        it "can insert records":
            connection.insert("users", { id: 1, name: "Test" })
            expect connection.count("users") == 1

        it "clears before each test":
            expect connection.count("users") == 0
```

### Pattern 3: Fixture Dependencies

```simple
context_def :math_fixtures:
    given_lazy :x, \:
        10

    given_lazy :y, \:
        x * 2  # y depends on x

    given_lazy :sum, \:
        x + y  # sum depends on both

describe "Math":
    context :math_fixtures:
        it "x is 10":
            expect x == 10

        it "y is 20 (x * 2)":
            expect y == 20

        it "sum is 30":
            expect sum == 30
```

### Pattern 4: API/Authentication Setup

```simple
context_def :authenticated:
    given_lazy :auth_token, \:
        "token_xyz123abc"

    given_lazy :user_id, \:
        42

context_def :with_rate_limit:
    given_lazy :requests_remaining, \:
        100

describe "API Endpoint":
    # Use single context
    context :authenticated:
        it "has auth token":
            expect auth_token.len > 0

        it "has user id":
            expect user_id == 42

    # Compose multiple contexts
    context_compose :authenticated, :with_rate_limit:
        it "authenticated with rate limit":
            expect auth_token.len > 0
            expect requests_remaining == 100
```

### Pattern 5: BDD Given-When-Then Style

```simple
context_def :calculator_state:
    given_lazy :calculator, \:
        { value: 0 }

describe "Calculator":
    context :calculator_state:
        # Given: calculator at zero
        it "starts at zero":
            expect calculator.value == 0

        # When: add 5
        context "after adding 5":
            given:
                calculator.value = calculator.value + 5

            # Then: value is 5
            it "has value of 5":
                expect calculator.value == 5

            # When: multiply by 2
            context "then multiply by 2":
                given:
                    calculator.value = calculator.value * 2

                # Then: value is 10
                it "has value of 10":
                    expect calculator.value == 10
```

### Pattern 6: Named Eager Fixtures - BDD "When" Setup (given :name)

You can name your eager setup blocks with `given :name, \: block`. This documents the "When" action in BDD Given-When-Then and creates parallel syntax to `given_lazy`:

```simple
describe "API Tests":
    context "with infrastructure":
        # Given: initial fixtures
        given_lazy :config, \:
            load_config()

        # When: setup database and cache
        given :database_setup, \:
            db.connect()
            db.migrate()

        given :cache_setup, \:
            cache.clear()

        # Then: verify setup complete
        it "database is ready":
            expect true

        it "cache is empty":
            expect true
```

**BDD Pattern:**
- **Given** (`given_lazy`) - Initial test data/state
- **When** (`given :name`) - Setup actions that prepare the test environment
- **Then** (`it`) - Assertions that verify behavior

**Key Points:**
- Named `given` runs eagerly (before each example) - not memoized
- Documents the "When" action in BDD Given-When-Then pattern
- Works in both `context_def` and regular `context` blocks
- Parallel syntax to `given_lazy :name, \: ...`
- Multiple `given :name` blocks run in order before each example

### Pattern 7: Sequential Given Blocks - Contexts + Variables

You can create complex setup sequences in `given:` blocks by combining context references with variable definitions:

```simple
context_def :user_data:
    given_lazy :user, \:
        { name: "Alice", email: "alice@example.com", id: 42 }

context_def :db_setup:
    given:
        # Simulate: db.connect(), db.migrate()
        pass

describe "Integrated Setup":
    context "with sequential given block":
        # Single given: block with multiple sequential steps
        given:
            # Step 1: Apply database setup from context_def
            given :db_setup

            # Step 2: Apply user fixtures from context_def
            given :user_data

            # Step 3: Define derived variables from fixtures
            let user_key = "user_" + user.id.to_string()
            let welcome_msg = "Welcome, " + user.name
            let contact = user.email

        # Then: all variables are available
        it "has user from context":
            expect user.name == "Alice"

        it "has derived variables from fixtures":
            expect user_key == "user_42"
            expect welcome_msg == "Welcome, Alice"

        it "can use any combination of fixtures and variables":
            expect contact == "alice@example.com"
```

**Sequential Execution:**
1. `given :context_name` - applies all givens from that context_def
2. `let variable = value` - defines new variables (can reference fixtures)
3. Each subsequent statement can use previous results
4. All executes before each example

**Key Points:**
- `given :context_name` applies all givens from that context_def
- Mix context references and variable definitions in any order
- Derived variables can reference fixtures from contexts
- All statements in `given:` block run sequentially before each example
- Fresh execution for each test (no sharing between examples)

### Pattern 8: Inline Lazy Fixtures (given_lazy in Regular Context)

`given_lazy` now works inline in regular `context` blocks, not just in `context_def`. This allows you to define lazy (memoized) fixtures without creating a separate context definition:

```simple
describe "User Service":
    context "with authenticated user":
        # Define lazy fixture inline (memoized per example)
        given_lazy :user, \:
            { id: 42, email: "user@example.com", role: "admin" }

        it "has user email":
            expect user.email == "user@example.com"

        it "user is same instance in example":
            # Same user object within this example
            expect user.id == 42

    context "with multiple fixtures":
        # Combine eager and lazy fixtures inline
        given:
            setup_test_database()

        given_lazy :config, \:
            { timeout: 30, retries: 3 }

        given_lazy :client, \:
            create_client(config)

        it "client uses config":
            expect client.timeout == 30
```

**Key Points:**
- `given_lazy` works in both `context_def` definitions AND regular `context` blocks
- Lazy fixtures are still memoized per example (called once, cached)
- Combine `given` (eager setup) with `given_lazy` (lazy fixtures) in the same block
- Useful for quick inline fixtures without defining a reusable context

## Comparing Old vs New

### Old Style (Still Supported)

```simple
describe "User":
    context "when user is admin":
        let user = { role: "admin" }

        it "has admin role":
            expect user.role == "admin"
```

### New Style (Context Sharing)

```simple
context_def :admin_user:
    given_lazy :user, \:
        { role: "admin" }

describe "User":
    context :admin_user:
        it "has admin role":
            expect user.role == "admin"
```

**Benefits of New Style:**
- Reuse `:admin_user` context in multiple test suites
- Lazy fixtures (memoized per example)
- Clearer separation of test data (Context definition) from tests

## Best Practices

### ✅ Do

- **Name contexts clearly**: `context_def :with_authenticated_user` not `context_def :ctx`
- **Name your setup blocks**: Use `given :db_setup, \: ...` when you have multiple setup steps
- **Use lazy fixtures by default**: `given_lazy` is memoized per example (better performance)
- **Use eager given for side effects**: `given { ... }` or `given :name, \: ...` for setup that must run
- **Compose related contexts**: `context_compose :db, :auth, :logging`
- **Keep contexts focused**: One concern per context
- **Mix fixture types**: Combine eager and lazy fixtures in one block for clarity

### ❌ Don't

- **Mix too many concerns**: Don't combine database + authentication + logging in one context
- **Overuse composition**: Composing 5+ contexts is hard to reason about
- **Mutate fixtures**: Fixtures should return fresh data
- **Create context dependencies**: One context shouldn't depend on another being defined first

## Fixture Types & BDD Pattern

| Type | Syntax | BDD Role | Timing | Use Case |
|------|--------|----------|--------|----------|
| **Unnamed eager** | `given { ... }` | When (setup) | Before each example | Simple setup, side effects |
| **Named eager** | `given :name, \: ...` | When (named action) | Before each example | Documented setup actions |
| **Named lazy** | `given_lazy :name, \: ...` | Given (state) | Per example (memoized) | Test data, fixtures |

**BDD Given-When-Then Pattern:**
```simple
context "with complete BDD pattern":
    # Given: test data/initial state (lazy - memoized)
    given_lazy :user, \:
        { id: 42, role: "admin" }

    # When: setup database (named eager)
    given :database_setup, \:
        db.connect()
        db.migrate()

    # When: initialize cache (unnamed eager)
    given:
        cache.clear()

    # Then: verify the behavior
    it "admin has correct permissions":
        expect user.role == "admin"

    it "each test gets fresh data":
        expect user.id == 42  # Same user (memoized)
```

**Execution Order:**
1. `given_lazy` fixtures are memoized once per example
2. `given :name` blocks run in order
3. `given { }` blocks run in order
4. Each `it` block executes
5. Fresh state for next example

## When to Use: context_def vs inline fixtures

| Scenario | Use | Example |
|----------|-----|---------|
| **Fixtures used in 1 test suite** | Inline `given_lazy` | `context "with user": given_lazy :user, ...` |
| **Fixtures used in 3+ test suites** | `context_def` + `context :name` | Reusable across files |
| **Simple test data** | Inline `given_lazy` | Quick fixtures without setup |
| **Complex setup** | `context_def` + `given` | Database, external service |
| **Multiple setup steps** | Named `given :name` | Clarity on what each setup does |
| **Composing fixtures** | `context_compose` | Multiple `context_def` definitions |
| **Both eager + lazy** | Mix `given` + `given_lazy` | `given :db, ... given_lazy :user, ...` |

## Common Patterns

### Setup and Teardown

```simple
context_def :database_session:
    given:
        db.connect()
        db.migrate()

    # No after_all needed - each test gets fresh data via given
    given_lazy :connection, \:
        db
```

### Multiple Test Data Variants

```simple
context_def :empty_list:
    given_lazy :items, \:
        []

context_def :list_with_items:
    given_lazy :items, \:
        [1, 2, 3, 4, 5]

describe "List Operations":
    context :empty_list:
        it "is empty":
            expect items.len == 0

    context :list_with_items:
        it "has items":
            expect items.len == 5
```

### Shared Complex Setup

```simple
context_def :user_with_orders:
    given_lazy :user, \:
        create_user("test@example.com")

    given_lazy :orders, \:
        [
            { id: 1, total: 100 },
            { id: 2, total: 200 }
        ]

    given_lazy :total_spent, \:
        orders.map(fn(o): o.total).sum()

describe "User Orders":
    context :user_with_orders:
        it "has 2 orders":
            expect orders.len == 2

        it "spent 300 total":
            expect total_spent == 300
```

## Migration Guide: From let to Context Sharing

If you're currently using `let` and want to share fixtures across test files:

### Before (No Sharing)

```simple
# string_spec.spl
describe "String Operations":
    let str = "hello world"
    it "has correct length":
        expect str.len == 11

# array_spec.spl
describe "Array Operations":
    let arr = [1, 2, 3]
    it "has length":
        expect arr.len == 3
```

### After (With Sharing)

```simple
# test_fixtures.spl
context_def :string_fixtures:
    given_lazy :str, \:
        "hello world"

context_def :array_fixtures:
    given_lazy :arr, \:
        [1, 2, 3]

# string_spec.spl
describe "String Operations":
    context :string_fixtures:
        it "has correct length":
            expect str.len == 11

# array_spec.spl
describe "Array Operations":
    context :array_fixtures:
        it "has length":
            expect arr.len == 3
```

## Troubleshooting

### Issue: Fixture not available in example

**Solution:** Make sure you're using `given_lazy` for the fixture:

```simple
# Wrong - fixture won't be available
context_def :my_context:
    given_lazy :value, \:
        42
    # Forget to reference it

# Correct
context :my_context:
    it "has value":
        expect value == 42  # value is available
```

### Issue: Fixture is being reused across examples

**Solution:** Lazy fixtures are memoized per example. If you need fresh data, use `given` instead:

```simple
context_def :counter:
    # Wrong - count is memoized
    given_lazy :count, \:
        0

# Right - count is fresh
context_def :counter:
    given:
        let count = 0  # Fresh per example
```

### Issue: Undefined context error

**Solution:** Make sure context is defined before use:

```simple
# Context must be defined
context_def :my_context:
    given_lazy :value, \:
        42

describe "Tests":
    context :my_context:  # Now it exists
        it "works":
            expect value == 42
```

## See Also

- [BDD Spec Framework Specification](../spec/testing/testing_bdd_framework.md#36-reusable-contexts-context-sharing)
- [Example Test Files](simple/std_lib/test/unit/spec/context_sharing_spec.spl)
- [Usage Examples](simple/std_lib/test/unit/spec/context_sharing_examples.spl)
