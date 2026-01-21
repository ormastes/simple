# Mocking Guide

**Status:** Implemented (Phase 3 - Basic version)
**Library:** `std.testing.mock`

## Overview

The mock library provides test doubles for verifying interactions with dependencies. This basic implementation tracks function calls and return values without requiring trait objects.

## Quick Start

### Basic Mock

```simple
import std.testing.mock as mock

fn test_user_service():
    # Create a mock
    val save_mock = mock.create_mock("save_user")

    # Simulate function call
    save_mock.record_call(["user123", "Alice"])

    # Verify it was called
    expect save_mock.was_called()
    expect save_mock.call_count() == 1
    expect save_mock.was_called_with(["user123", "Alice"])
```

## Creating Mocks

### Method 1: Simple Creation

```simple
val mock = mock.create_mock("function_name")
```

### Method 2: With Return Values

```simple
val mock = mock.MockBuilder.new("get_user")
    .returns(["Alice", "Bob", "Charlie"])

# Get return values in sequence
match mock.next_return_value():
    Some(v): print v  # → "Alice"
    None: print "No more values"
```

### Method 3: Mock That Panics

```simple
val mock = mock.MockBuilder.new("fail_operation")
    .panics("Database connection failed")

# Mock is configured to panic when called
```

## Recording Calls

Track function invocations:

```simple
val mock = mock.create_mock("save_data")

# Record calls (arguments as strings)
mock.record_call(["arg1", "arg2"])
mock.record_call(["arg3"])

print mock.call_count()  # → 2
```

## Verification

### Was Called

```simple
if mock.was_called():
    print "Function was invoked"
```

### Called N Times

```simple
expect mock.was_called_n_times(3)
expect mock.call_count() == 3
```

### Called With Arguments

```simple
expect mock.was_called_with(["expected", "args"])
```

### Helper Functions

```simple
# Verify call count
expect mock.verify_called(mock, 5)

# Verify arguments
expect mock.verify_called_with(mock, ["user123"])
```

## Inspecting Calls

### Get Specific Call

```simple
match mock.get_call(0):  # First call (0-indexed)
    Some(call):
        print "Call #{call.call_number}"
        print "Args: {call.args}"
    None:
        print "No such call"
```

### Get Last Call

```simple
match mock.get_last_call():
    Some(call):
        print "Last call args: {call.args}"
    None:
        print "No calls recorded"
```

### Iterate All Calls

```simple
val mock = mock.create_mock("process")
mock.record_call(["data1"])
mock.record_call(["data2"])

for i in 0..mock.call_count():
    match mock.get_call(i):
        Some(call): print call.args
        None: break
```

## Mock Registry

Manage multiple mocks:

```simple
val registry = mock.MockRegistry.new()

# Register mocks
val save_mock = mock.create_mock("save")
val load_mock = mock.create_mock("load")

registry.register("save", save_mock)
registry.register("load", load_mock)

# Simulate operations
save_mock.record_call(["data"])
load_mock.record_call(["key"])

# Get summary
print registry.summary()

# Reset all mocks
registry.reset_all()
```

## Return Values

Simulate function returns:

```simple
val mock = mock.MockBuilder.new("fetch_data")
    .returns(["result1", "result2", "result3"])

# First call
match mock.next_return_value():
    Some(v): print v  # → "result1"
    None: pass

# Second call
match mock.next_return_value():
    Some(v): print v  # → "result2"
    None: pass

# When exhausted
match mock.next_return_value():
    None: print "No more values"
    Some(_): pass
```

## Resetting Mocks

Clear call history:

```simple
val mock = mock.create_mock("operation")

mock.record_call(["arg1"])
mock.record_call(["arg2"])
print mock.call_count()  # → 2

mock.reset()
print mock.call_count()  # → 0
```

## Real-World Examples

### Example 1: Testing a Service

```simple
import std.testing.mock as mock

fn test_user_service_saves_user():
    # Setup: Create mock repository
    val repo_mock = mock.create_mock("user_repository.save")

    # Execute: Call service (which uses repository)
    val service = UserService(repository: repo_mock)
    service.create_user("user123", "Alice")

    # Verify: Repository was called correctly
    expect repo_mock.was_called()
    expect repo_mock.was_called_with(["user123", "Alice"])
```

### Example 2: Testing API Client

```simple
fn test_api_client():
    val http_mock = mock.MockBuilder.new("http_client")
        .returns([
            '{"status": "ok"}',
            '{"status": "error"}'
        ])

    # First request succeeds
    match http_mock.next_return_value():
        Some(response):
            http_mock.record_call(["GET", "/api/users"])
            print "Response: {response}"
        None: fail "Expected response"

    # Verify
    expect http_mock.was_called_with(["GET", "/api/users"])
```

### Example 3: Dependency Injection

```simple
# Application code
class EmailService:
    mailer: MockFunction  # In real code, this would be a trait

    fn send_welcome(user_id: text):
        # Send email (using mock in tests)
        self.mailer.record_call(["welcome", user_id])
        # In real implementation, use mailer.next_return_value()

# Test code
fn test_email_service():
    val mailer_mock = mock.MockBuilder.new("mailer")
        .returns(["sent"])

    val service = EmailService(mailer: mailer_mock)
    service.send_welcome("user123")

    expect mailer_mock.was_called_with(["welcome", "user123"])
```

## Best Practices

### 1. Mock External Dependencies Only

❌ **Don't mock internal logic:**
```simple
# Bad: Mocking internal helper
val helper_mock = mock.create_mock("internal_helper")
```

✅ **Mock external dependencies:**
```simple
# Good: Mocking database, HTTP client, file system
val db_mock = mock.create_mock("database")
val http_mock = mock.create_mock("http_client")
```

### 2. Use Descriptive Names

❌ **Vague names:**
```simple
val m1 = mock.create_mock("fn")
```

✅ **Clear names:**
```simple
val user_repo_mock = mock.create_mock("user_repository.save")
val email_sender_mock = mock.create_mock("email_service.send")
```

### 3. Verify What Matters

❌ **Over-verification:**
```simple
# Don't verify every single call
expect mock.was_called()
expect mock.call_count() == 1
expect mock.was_called_n_times(1)
expect mock.was_called_with(args)
```

✅ **Verify behavior:**
```simple
# Verify the important interaction
expect mock.was_called_with(["user123", "Alice"])
```

### 4. Reset Between Tests

```simple
fn test_operation_a():
    val mock = mock.create_mock("op")
    mock.record_call(["a"])
    expect mock.call_count() == 1

fn test_operation_b():
    val mock = mock.create_mock("op")  # Fresh mock
    mock.record_call(["b"])
    expect mock.call_count() == 1
```

### 5. Use Registry for Complex Tests

```simple
fn test_complex_workflow():
    val registry = mock.MockRegistry.new()

    # Setup all mocks
    val db_mock = mock.create_mock("db")
    val cache_mock = mock.create_mock("cache")
    val email_mock = mock.create_mock("email")

    registry.register("db", db_mock)
    registry.register("cache", cache_mock)
    registry.register("email", email_mock)

    # ... test logic ...

    # Easy cleanup
    registry.reset_all()
}
```

## Limitations

### 1. No Automatic Mocking

Unlike languages with reflection, you must manually:
- Create mocks
- Call `record_call()` in your code
- Track return values

**Workaround:** Use dependency injection to pass mocks.

### 2. Arguments Are Strings

All arguments are stored as text:

```simple
# Must convert to strings
mock.record_call(["123", "true", "Alice"])

# Not type-safe
mock.was_called_with(["123"])  # OK
mock.was_called_with([123])    # Wrong type
```

**Future:** Will improve when trait objects are available.

### 3. No Trait Object Support

Cannot create mocks that implement traits directly.

**Workaround:** Explicitly pass mock to code under test.

### 4. Manual Call Recording

You must manually call `record_call()`:

```simple
# Your code must explicitly record calls
fn save_user(mock: MockFunction, user_id: text):
    mock.record_call([user_id])
    # ... actual logic ...
```

**Future:** Automatic call interception when language supports it.

## Troubleshooting

### Problem: Mock Not Recording Calls

**Symptoms:**
```simple
expect mock.was_called()  # Fails!
```

**Solutions:**
1. Ensure you're calling `mock.record_call()`
2. Check mock reference (ensure you're using the same instance)
3. Verify test execution order

### Problem: Wrong Call Count

**Symptoms:**
```simple
expect mock.call_count() == 1  # Fails, count is 3
```

**Solutions:**
1. Reset mock between tests
2. Check for extra calls
3. Use `mock.summary()` to see all calls

### Problem: Arguments Don't Match

**Symptoms:**
```simple
expect mock.was_called_with(["user123"])  # Fails
```

**Solutions:**
1. Print call history: `print mock.summary()`
2. Check argument order
3. Ensure arguments are strings
4. Use `get_last_call()` to inspect actual arguments

## Advanced Patterns

### Pattern 1: Spy (Partial Mock)

Track calls but use real implementation:

```simple
val spy = mock.create_mock("real_function")

fn call_with_spy(arg: text) -> text:
    spy.record_call([arg])
    real_function(arg)  # Call real implementation
```

### Pattern 2: Stub (Pre-configured Responses)

```simple
val stub = mock.MockBuilder.new("config_service")
    .returns([
        '{"api_key": "test123"}',
        '{"timeout": "30"}'
    ])

# Use stub in tests without assertions
```

### Pattern 3: Fake (Simple Implementation)

```simple
class FakeDatabase:
    calls: MockFunction
    data: Map<text, text>

    fn save(key: text, value: text):
        self.calls.record_call([key, value])
        self.data.insert(key, value)

    fn load(key: text) -> Option<text>:
        self.calls.record_call([key])
        self.data.get(key)
```

## Examples

See `simple/std_lib/examples/testing/mock_example.spl` for complete examples.

## API Reference

### Types

**`MockFunction`**
- `new(name)` - Create mock
- `record_call(args)` - Record invocation
- `set_return_values(values)` - Configure returns
- `next_return_value()` - Get next return
- `call_count()` - Get call count
- `was_called()` - Check if called
- `was_called_with(args)` - Check arguments
- `get_call(index)` - Get specific call
- `reset()` - Clear history

**`MockBuilder`**
- `new(name)` - Create builder
- `returns(values)` - Set return values
- `panics(message)` - Configure panic
- `build()` - Create mock

**`MockRegistry`**
- `new()` - Create registry
- `register(name, mock)` - Add mock
- `get(name)` - Retrieve mock
- `reset_all()` - Reset all mocks
- `summary()` - Get summary

### Functions

- `create_mock(name)` - Create simple mock
- `verify_called(mock, times)` - Verify call count
- `verify_called_with(mock, args)` - Verify arguments
