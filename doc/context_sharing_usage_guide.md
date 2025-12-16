# Context Sharing Usage Guide

A guide to using reusable Contexts with given fixtures in the Simple BDD spec framework.

## Overview

Context Sharing allows you to define reusable test setup (fixtures) once and use them across multiple test groups. This reduces duplication and improves test maintainability.

## Basic Syntax

### 1. Define a Reusable Context

```simple
Context :context_name:
    given_lazy :fixture_name, fn():
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
Context :user_fixtures:
    given_lazy :admin_user, fn():
        { name: "Admin", role: "admin", permissions: ["read", "write", "delete"] }

    given_lazy :regular_user, fn():
        { name: "User", role: "user", permissions: ["read"] }

# Use it in multiple places
describe "User Permissions":
    context :user_fixtures:
        it "admin has delete permission":
            expect admin_user.permissions.includes?("delete")

        it "regular user has no delete":
            expect not regular_user.permissions.includes?("delete")
```

### Pattern 2: Database/External Service Setup

```simple
Context :with_database:
    # Eager given - setup runs before each test
    given:
        db.clear_tables()

    # Lazy given - connection is memoized
    given_lazy :connection, fn():
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
Context :math_fixtures:
    given_lazy :x, fn():
        10

    given_lazy :y, fn():
        x * 2  # y depends on x

    given_lazy :sum, fn():
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
Context :authenticated:
    given_lazy :auth_token, fn():
        "token_xyz123abc"

    given_lazy :user_id, fn():
        42

Context :with_rate_limit:
    given_lazy :requests_remaining, fn():
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
Context :calculator_state:
    given_lazy :calculator, fn():
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
Context :admin_user:
    given_lazy :user, fn():
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

- **Name contexts clearly**: `Context :with_authenticated_user` not `Context :ctx`
- **Use lazy fixtures by default**: `given_lazy` is memoized per example
- **Use eager given for setup**: `given { }` for database clearing, file cleanup, etc.
- **Compose related contexts**: `context_compose :db, :auth, :logging`
- **Keep contexts focused**: One concern per context
- **Document context purpose**: Add comments explaining what fixtures it provides

### ❌ Don't

- **Mix too many concerns**: Don't combine database + authentication + logging in one context
- **Overuse composition**: Composing 5+ contexts is hard to reason about
- **Mutate fixtures**: Fixtures should return fresh data
- **Create context dependencies**: One context shouldn't depend on another being defined first

## Common Patterns

### Setup and Teardown

```simple
Context :database_session:
    given:
        db.connect()
        db.migrate()

    # No after_all needed - each test gets fresh data via given
    given_lazy :connection, fn():
        db
```

### Multiple Test Data Variants

```simple
Context :empty_list:
    given_lazy :items, fn():
        []

Context :list_with_items:
    given_lazy :items, fn():
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
Context :user_with_orders:
    given_lazy :user, fn():
        create_user("test@example.com")

    given_lazy :orders, fn():
        [
            { id: 1, total: 100 },
            { id: 2, total: 200 }
        ]

    given_lazy :total_spent, fn():
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
Context :string_fixtures:
    given_lazy :str, fn():
        "hello world"

Context :array_fixtures:
    given_lazy :arr, fn():
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
Context :my_context:
    given_lazy :value, fn():
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
Context :counter:
    # Wrong - count is memoized
    given_lazy :count, fn():
        0

# Right - count is fresh
Context :counter:
    given:
        let count = 0  # Fresh per example
```

### Issue: Undefined context error

**Solution:** Make sure context is defined before use:

```simple
# Context must be defined
Context :my_context:
    given_lazy :value, fn():
        42

describe "Tests":
    context :my_context:  # Now it exists
        it "works":
            expect value == 42
```

## See Also

- [BDD Spec Framework Specification](doc/spec/bdd_spec.md#36-reusable-contexts-context-sharing)
- [Example Test Files](simple/std_lib/test/unit/spec/context_sharing_spec.spl)
- [Usage Examples](simple/std_lib/test/unit/spec/context_sharing_examples.spl)
