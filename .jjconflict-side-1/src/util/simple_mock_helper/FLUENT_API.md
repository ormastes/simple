# Fluent Mock API

Fluent/chainable API for mock setup and verification in the `simple_mock_helper` library.

## Overview

The fluent API provides a builder-style interface for configuring mocks and verifying their behavior, inspired by modern mocking frameworks like RSpec, Mockito, and Jest.

## Features

- **Chainable method calls** - Natural, readable test code
- **Flexible argument matching** - Any, exact, greater than, less than, ranges, patterns
- **Multiple return values** - Sequential returns, single returns
- **Call count verification** - Exact, at least, at most, never
- **Spy support** - Record and verify method calls
- **Type-safe** - Compile-time checking where possible

## Core Types

### `MockSetup`

Builder for setting up mock behavior.

```rust
use simple_mock_helper::fluent::{MockSetup, ArgMatcher};

let mut setup = MockSetup::new("UserDao");

// Configure methods
setup.when("findById")
    .with_args(&[123])
    .returns("User(id: 123)")
    .times(1);

setup.when("save")
    .with_any_args()
    .returns("true");
```

### `MockVerify`

Builder for verifying mock calls.

```rust
use simple_mock_helper::fluent::MockVerify;

let mut verify = MockVerify::new("UserDao");

verify.method("findById")
    .was_called()
    .with_args(&[123])
    .once();

// Verify all expectations
if let Err(errors) = verify.verify_all() {
    for error in errors {
        eprintln!("Verification failed: {}", error);
    }
}
```

### `Spy`

Records method calls for later verification.

```rust
use simple_mock_helper::fluent::Spy;

let mut spy = Spy::new("UserService");

// Record calls
spy.record("createUser", vec!["Alice"]);
spy.record("createUser", vec!["Bob"]);
spy.record("deleteUser", vec!["Alice"]);

// Verify
assert_eq!(spy.call_count("createUser"), 2);
assert_eq!(spy.call_count("deleteUser"), 1);

let create_calls = spy.get_calls("createUser");
assert_eq!(create_calls.len(), 2);
```

## Method Setup API

### Creating Setup

```rust
let mut setup = MockSetup::new("MockName");
let method = setup.when("methodName");
```

### Argument Matching

```rust
// Match any arguments
method.with_any_args();

// Match specific arguments
method.with_args(&[123, "test"]);

// Match using matchers
method.with_matchers(vec![
    ArgMatcher::Any,
    ArgMatcher::GreaterThan(10),
    ArgMatcher::LessThan(100),
    ArgMatcher::Range(10, 100),
    ArgMatcher::Pattern("user.*".to_string()),
]);
```

### Return Values

```rust
// Return same value for all calls
method.returns("value");

// Return different values in sequence
method.returns_once("first")
      .returns_once("second")
      .returns_once("third");

// Or use returns_seq
method.returns_seq(vec!["first", "second", "third"]);
```

### Side Effects

```rust
// Execute side effects on call
method.does("log('called')")
      .does("increment_counter()");
```

### Deep Call Chains

```rust
// Mock nested method calls
method.chain("getManager")
      .chain("getName")
      .returns("Alice");

// Full example: library.getHeadLibrarian().getName()
setup.when("getHeadLibrarian")
    .chain("getName")
    .returns("Jane Doe");

// With arguments: company.getDepartment("Engineering").getManager().getName()
setup.when("getDepartment")
    .chain("getManager")
    .chain("getName")
    .with_args(&["Engineering"])
    .returns("Alice Smith");

// Get full path
assert_eq!(method.full_method_path(), "getHeadLibrarian().getName");
```

### Call Count Expectations

```rust
// Expect specific number of calls
method.times(3);

// Expect at least one call
method.at_least_once();
```

### Exceptions

```rust
// Make method throw an exception
method.throws("Error: not found");
```

## Verification API

### Creating Verification

```rust
let mut verify = MockVerify::new("MockName");
let method = verify.method("methodName");
```

### Verification Expectations

```rust
// Verify was called at least once
method.was_called();

// Verify was never called
method.was_not_called();

// Verify exact number of calls
method.times(3);

// Verify at least n calls
method.at_least(2);

// Verify at most n calls
method.at_most(5);

// Verify called exactly once
method.once();
```

### Argument Verification

```rust
// Verify with specific arguments
method.with_args(&[123, "test"]);

// Verify with matchers
method.with_matchers(vec![
    ArgMatcher::Any,
    ArgMatcher::GreaterThan(0),
]);
```

### Performing Verification

```rust
// Verify individual method
method.set_actual_calls(3);
match method.verify() {
    Ok(()) => println!("Verification passed"),
    Err(e) => eprintln!("Verification failed: {}", e),
}

// Verify all methods at once
match verify.verify_all() {
    Ok(()) => println!("All verifications passed"),
    Err(errors) => {
        for error in errors {
            eprintln!("Verification failed: {}", error);
        }
    }
}
```

## Argument Matchers

### `ArgMatcher::Any`

Matches any value.

```rust
method.with_matchers(vec![ArgMatcher::Any]);
```

### `ArgMatcher::Exact(value)`

Matches exact value.

```rust
method.with_args(&[123]); // Creates Exact matchers
```

### `ArgMatcher::GreaterThan(n)`

Matches values greater than n.

```rust
method.with_matchers(vec![ArgMatcher::GreaterThan(10)]);
```

### `ArgMatcher::LessThan(n)`

Matches values less than n.

```rust
method.with_matchers(vec![ArgMatcher::LessThan(100)]);
```

### `ArgMatcher::Range(min, max)`

Matches values in range [min, max].

```rust
method.with_matchers(vec![ArgMatcher::Range(10, 100)]);
```

### `ArgMatcher::Pattern(pattern)`

Matches values against regex pattern.

```rust
method.with_matchers(vec![ArgMatcher::Pattern("user.*".to_string())]);
```

### `ArgMatcher::Predicate(description)`

Custom predicate matcher.

```rust
method.with_matchers(vec![ArgMatcher::Predicate("is_even".to_string())]);
```

## Complete Example

```rust
use simple_mock_helper::fluent::{MockSetup, MockVerify, ArgMatcher, Spy};

#[test]
fn test_user_service() {
    // Setup mocks
    let mut dao_setup = MockSetup::new("UserDao");
    dao_setup.when("findById")
        .with_args(&[123])
        .returns("User(id: 123, name: 'Alice')")
        .times(1);
    
    dao_setup.when("save")
        .with_matchers(vec![ArgMatcher::Any])
        .returns("true")
        .at_least_once();
    
    // Setup spy
    let mut notifier_spy = Spy::new("Notifier");
    
    // Exercise system under test
    // ... (call your service methods) ...
    
    // Simulate recording calls
    notifier_spy.record("notify", vec!["user.created", "123"]);
    
    // Verify
    let mut dao_verify = MockVerify::new("UserDao");
    dao_verify.method("findById")
        .was_called()
        .with_args(&[123])
        .once();
    
    dao_verify.method("save")
        .was_called()
        .at_least(1);
    
    // Verify all
    assert!(dao_verify.verify_all().is_ok());
    
    // Verify spy
    assert_eq!(notifier_spy.call_count("notify"), 1);
    let notify_calls = notifier_spy.get_calls("notify");
    assert_eq!(notify_calls[0][0], "user.created");
    assert_eq!(notify_calls[0][1], "123");
}
```

## Deep Call Chain Example

```rust
use simple_mock_helper::fluent::MockSetup;

#[test]
fn test_deep_call_chains() {
    let mut setup = MockSetup::new("Library");
    
    // Simple chain: library.getHeadLibrarian().getName()
    setup.when("getHeadLibrarian")
        .chain("getName")
        .returns("Jane Doe");
    
    // Multiple chains: company.getDepartment("Eng").getManager().getName()
    setup.when("getDepartment")
        .chain("getManager")
        .chain("getName")
        .with_args(&["Engineering"])
        .returns("Alice Smith");
    
    // Verify the chains
    assert_eq!(setup.setups()[0].full_method_path(), "getHeadLibrarian().getName");
    assert_eq!(setup.setups()[1].full_method_path(), "getDepartment().getManager().getName");
    
    // Display shows the full chain
    println!("{}", setup.setups()[0]); // Library::getHeadLibrarian().getName -> Jane Doe
}
```

## Design Principles

1. **Chainable** - Methods return `&mut Self` for fluent chaining
2. **Readable** - DSL reads like natural language
3. **Type-safe** - Compile-time checking where possible
4. **Flexible** - Support for various matching strategies
5. **Discoverable** - IDE autocomplete-friendly

## Comparison with Other Frameworks

### RSpec-style (Ruby)

```ruby
allow(user_dao).to receive(:find_by_id).with(123).and_return(user)
expect(user_dao).to have_received(:find_by_id).with(123).once
```

### Mockito-style (Java)

```java
when(userDao.findById(123)).thenReturn(user);
verify(userDao, times(1)).findById(123);
```

### Simple fluent style (Rust)

```rust
setup.when("findById").with_args(&[123]).returns(user).times(1);
verify.method("findById").was_called().with_args(&[123]).once();
```

## Integration with Test Framework

The fluent API is designed to work alongside the existing mock policy system:

```rust
use simple_mock_helper::{init_mocks_for_only, check_mock_use_from};
use simple_mock_helper::fluent::{MockSetup, MockVerify};

#[ctor::ctor]
fn init_mock_policy() {
    init_mocks_for_only(&["*"]);
}

#[test]
fn test_with_fluent_mocks() {
    check_mock_use_from(module_path!());
    
    let mut setup = MockSetup::new("MyMock");
    setup.when("method").returns("value");
    
    // ... test code ...
    
    let mut verify = MockVerify::new("MyMock");
    verify.method("method").was_called();
    assert!(verify.verify_all().is_ok());
}
```

## Future Enhancements

- **Async support** - Mock async methods and futures
- **Callback support** - Execute callbacks on method calls
- **Order verification** - Verify methods called in specific order
- **Invocation matchers** - More sophisticated argument matching
- **Auto-reset** - Automatic cleanup between tests
- **Recording mode** - Record real calls for replay

## See Also

- [Mock Policy Documentation](../README.md#mock-policy)
- [Test Levels](../README.md#test-levels-and-coverage-metrics)
- [Coverage Tools](../README.md#classstruct-public-method-coverage)
