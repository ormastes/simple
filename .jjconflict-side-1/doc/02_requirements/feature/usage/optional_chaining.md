# Optional Chaining Specification
*Source:* `test/feature/usage/optional_chaining_spec.spl`
**Feature IDs:** #OPERATORS-OPTIONAL-CHAIN  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



Optional chaining (`?.`) provides safe navigation through potentially-nil
values in object graphs and method call chains. It automatically propagates
None values through the chain without requiring manual null checks at each step.

## Syntax

```simple
obj?.field               # Safe field access - returns Option
obj?.method()            # Safe method call - returns Option
obj?.field?.nested?.deep # Safe chaining - short-circuits on None
```

## Key Behaviors

- Optional chaining returns Option<T> for chained operations
- Returns None immediately if any intermediate value is None
- Prevents null pointer exceptions and NullPointerException-style errors
- Works with both field access and method calls
- Can be chained multiple times
- Integrates with null coalescing (`??`) for fallback values

## Feature: Optional Chaining

Verifies that optional chaining operator (`?.`) safely navigates object
    graphs and method chains. Tests cover field access, method calls, chaining
    multiple operations, and integration with null coalescing.

### Scenario: optional field access

| # | Example | Status |
|---|---------|--------|
| 1 | returns Some when value is present | pass |
| 2 | returns None when intermediate value is None | pass |
| 3 | works with deeply nested structures | pass |
| 4 | short-circuits on first None in chain | pass |

**Example:** returns Some when value is present
    Given val profile_obj = Profile(bio: "Hello")
    Given val user = User(name: "Alice", profile: Some(profile_obj))
    Given val result = user.profile?.bio
    Then  expect result == Some("Hello")

**Example:** returns None when intermediate value is None
    Given val user = User(name: "Bob", profile: None)
    Given val result = user.profile?.bio
    Then  expect result == None

**Example:** works with deeply nested structures
    Given val user = User(profile: Some(Profile(address: Some(Address(city: "NYC")))))
    Given val profile_opt = user.profile
    Then  expect profile_opt != None

**Example:** short-circuits on first None in chain
    Given val user = User(profile: None)
    Given val result = user.profile?.address?.city
    Then  expect result == None

### Scenario: optional method calls

| # | Example | Status |
|---|---------|--------|
| 1 | calls method when value is Some | pass |
| 2 | returns None when Option is None | pass |
| 3 | works with chained method calls | pass |
| 4 | handles methods with parameters | pass |

**Example:** calls method when value is Some
    Given val opt = Some(Container(value: 21))
    Given val result = opt?.get_doubled()
    Then  expect result == Some(42)

**Example:** returns None when Option is None
    Given val opt: Option<Container> = None
    Given val result = opt?.get_doubled()
    Then  expect result == None

**Example:** works with chained method calls
    Given val wrapped = Wrapper(value: 1)
    Given val opt = Some(wrapped)
    Given val result = opt?.increment()?.increment()
    Then  expect result == Some(Wrapper(value: 3))

**Example:** handles methods with parameters
    Given val calc_opt = Some(Calculator(value: 10))
    Given val result = calc_opt?.add(5)
    Then  expect result == Some(15)

### Scenario: chaining field and method access

| # | Example | Status |
|---|---------|--------|
| 1 | combines field and method access | pass |
| 2 | chains field access followed by field access | pass |

**Example:** combines field and method access
    Given val container = Container(data: Some(Data(count: 5)))
    Given val result = container.data?.double_count()
    Then  expect result == Some(10)

**Example:** chains field access followed by field access
    Given val outer = Outer(middle: Middle(inner: Some(Inner(name: "test"))))
    Given val result = outer.middle.inner?.name
    Then  expect result == Some("test")

### Scenario: with null coalescing operator

| # | Example | Status |
|---|---------|--------|
| 1 | provides fallback when chaining returns None | pass |
| 2 | uses actual value when chaining succeeds | pass |
| 3 | chains multiple fallbacks | pass |

**Example:** provides fallback when chaining returns None
    Given val user: User = User(profile: None)
    Given val result = user.profile?.bio ?? "No bio"
    Then  expect result == "No bio"

**Example:** uses actual value when chaining succeeds
    Given val user = User(profile: Some(Profile(bio: "Developer")))
    Given val result = user.profile?.bio ?? "No bio"
    Then  expect result == "Developer"

**Example:** chains multiple fallbacks
    Given val user = User(settings: None)
    Given val result = user.settings?.theme ?? "dark"
    Then  expect result == "dark"

### Scenario: type preservation

| # | Example | Status |
|---|---------|--------|
| 1 | wraps return value in Option | pass |
| 2 | preserves complex types through chaining | pass |

**Example:** wraps return value in Option
    Given val service_opt = Some(Service())
    Given val result = service_opt?.status()
    Then  expect result == Some(200)

**Example:** preserves complex types through chaining
    Given val container_opt = Some(DataContainer(items: [1, 2, 3]))
    Given val result = container_opt?.get_items()
    Then  expect result == Some([1, 2, 3])

### Scenario: integration with other features

| # | Example | Status |
|---|---------|--------|
| 1 | works with collection methods | pass |
| 2 | handles None in collection operations | pass |

**Example:** works with collection methods
    Given val inventory_opt = Some(Inventory(items: [Item(name: "sword"), Item(name: "shield")]))
    Given val result = inventory_opt?.find_item("sword")
    Then  expect result == Some(Item(name: "sword"))

**Example:** handles None in collection operations
    Given val inventory_opt: Option<Inventory> = None
    Given val result = inventory_opt?.find_item("sword")
    Then  expect result == None

### Scenario: practical usage patterns

| # | Example | Status |
|---|---------|--------|
| 1 | simplifies conditional access patterns | pass |
| 2 | provides defensive programming in data processing | pass |
| 3 | enables safe navigation in unknown data structures | pass |

**Example:** simplifies conditional access patterns
    Given val user = User(name: "Alice", email: Some("alice@example.com"))
    Given val email = user.email?.upper()
    Then  expect email == Some("ALICE@EXAMPLE.COM")

**Example:** provides defensive programming in data processing
    Given val log = LogEntry(message: "Error", details: Some("File not found"))
    Given val detail = log.details
    Then  expect detail == Some("File not found")

**Example:** enables safe navigation in unknown data structures
    Given val config = Config(settings: Some({"key": "value"}))
    Given val key_exists = config.settings?.get("key")
    Then  expect key_exists == Some("value")


