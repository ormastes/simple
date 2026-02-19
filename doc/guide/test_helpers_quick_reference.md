# Test Helpers Quick Reference
**Quick lookup for Simple testing utilities**

## Import

```simple
import testing  # All helpers available
```

---

## Assertion Helpers

### Equality

| Function | Usage | Returns |
|----------|-------|---------|
| `assert_eq(actual, expected, msg)` | Assert values are equal | `void` (panics if not equal) |
| `assert_ne(actual, unexpected, msg)` | Assert values are not equal | `void` (panics if equal) |

```simple
testing.assert_eq(result, 42, "Should be 42")
testing.assert_ne(result, 0, "Should not be zero")
```

### Boolean

| Function | Usage | Returns |
|----------|-------|---------|
| `assert_true(condition, msg)` | Assert condition is true | `void` (panics if false) |
| `assert_false(condition, msg)` | Assert condition is false | `void` (panics if true) |

```simple
testing.assert_true(user.is_active(), "User should be active")
testing.assert_false(user.is_deleted(), "User should not be deleted")
```

### Option

| Function | Usage | Returns |
|----------|-------|---------|
| `assert_some(option, msg)` | Assert Option is Some | `T` (unwrapped value) |
| `assert_none(option, msg)` | Assert Option is None | `void` (panics if Some) |

```simple
val user = testing.assert_some(find_user("id"), "User should exist")
testing.assert_none(find_user("invalid"), "Should not find user")
```

### Result

| Function | Usage | Returns |
|----------|-------|---------|
| `assert_ok(result, msg)` | Assert Result is Ok | `T` (unwrapped value) |
| `assert_err(result, msg)` | Assert Result is Err | `E` (error value) |

```simple
val data = testing.assert_ok(load_config(), "Config should load")
val error = testing.assert_err(invalid_op(), "Should fail")
```

---

## Timing Helpers

### Measure Time

| Function | Usage | Returns |
|----------|-------|---------|
| `measure_time(action)` | Measure execution time | `(T, i64)` (result, microseconds) |
| `assert_fast(action, max_micros, msg)` | Assert completes within time | `T` (result, panics if too slow) |

```simple
val (result, elapsed) = testing.measure_time(\: expensive_op())
print "Took {elapsed} μs"

val result = testing.assert_fast(
    \: query_db(),
    100000,  # 100ms limit
    "Query too slow"
)
```

---

## Mock Helpers

### Creating Mocks

| Function | Usage | Returns |
|----------|-------|---------|
| `create_spy(name)` | Create a spy/mock | `MockFunction` |

```simple
val spy = testing.create_spy("save_user")
spy.record_call(["user123", "Alice"])
```

### Verifying Mocks

| Function | Usage | Returns |
|----------|-------|---------|
| `assert_called(mock, times)` | Assert called N times | `void` (panics if wrong count) |
| `assert_called_with(mock, args)` | Assert called with args | `void` (panics if not found) |
| `assert_not_called(mock)` | Assert never called | `void` (panics if called) |

```simple
testing.assert_called(save_mock, 3)
testing.assert_called_with(save_mock, ["user123", "Alice"])
testing.assert_not_called(delete_mock)
```

---

## Collection Helpers

### Collection Assertions

| Function | Usage | Returns |
|----------|-------|---------|
| `assert_contains(list, item, msg)` | Assert item in collection | `void` (panics if not found) |
| `assert_not_contains(list, item, msg)` | Assert item not in collection | `void` (panics if found) |
| `assert_empty(list, msg)` | Assert collection is empty | `void` (panics if not empty) |
| `assert_len(list, expected, msg)` | Assert collection length | `void` (panics if wrong length) |

```simple
testing.assert_contains(users, "Alice", "Should contain Alice")
testing.assert_not_contains(users, "Bob", "Should not contain Bob")
testing.assert_empty(errors, "Should have no errors")
testing.assert_len(results, 5, "Should have 5 results")
```

---

## Fixture Helpers

### Setup/Teardown

| Function | Usage | Returns |
|----------|-------|---------|
| `with_cleanup(setup, teardown, test)` | Run test with fixture cleanup | `void` |
| `with_timeout(action, timeout_secs, msg)` | Run with timeout | `T` (result, panics if timeout) |

```simple
testing.with_cleanup(
    \: create_temp_file(),      # Setup
    \f: delete_file(f),          # Teardown
    \f: test_file_ops(f)         # Test
)

val result = testing.with_timeout(
    \: slow_operation(),
    5.0,  # 5 second timeout
    "Operation timed out"
)
```

---

## Common Patterns

### Pattern: Test with Option

```simple
val result = find_user("user123")
val user = testing.assert_some(result, "User should exist")
testing.assert_eq(user.name, "Alice", "Name should be Alice")
```

### Pattern: Test with Result

```simple
val result = load_config()
val config = testing.assert_ok(result, "Config should load")
testing.assert_eq(config.version, "1.0", "Version should be 1.0")
```

### Pattern: Test with Mock

```simple
val db_mock = testing.create_spy("database")
val service = UserService(db: db_mock)

service.save_user("user123", "Alice")

testing.assert_called(db_mock, 1)
testing.assert_called_with(db_mock, ["save", "user123", "Alice"])
```

### Pattern: Performance Test

```simple
val result = testing.assert_fast(
    \:
        var sum = 0
        for i in 0..1000:
            sum = sum + i
        sum
    ,
    10000,  # 10ms limit
    "Loop should be fast"
)
testing.assert_eq(result, 499500, "Sum should be correct")
```

### Pattern: Test with Cleanup

```simple
testing.with_cleanup(
    \:
        val db = Database.connect("test.db")
        db.init_schema()
        db
    ,
    \db:
        db.disconnect()
        delete_file("test.db")
    ,
    \db:
        val user = User.new("Alice")
        db.save(user)
        val loaded = testing.assert_some(
            db.load("Alice"),
            "Should load user"
        )
        testing.assert_eq(loaded.name, "Alice", "Name should match")
)
```

### Pattern: Collection Testing

```simple
val users = ["Alice", "Bob", "Charlie"]

testing.assert_len(users, 3, "Should have 3 users")
testing.assert_contains(users, "Alice", "Should have Alice")
testing.assert_not_contains(users, "David", "Should not have David")
```

### Pattern: Timing Measurement

```simple
val (result, elapsed) = testing.measure_time(\:
    sort_large_dataset(data)
)

print "Sorting took {elapsed} μs"
testing.assert_true(elapsed < 1000000, "Should take less than 1 second")
testing.assert_eq(result.len(), data.len(), "All items should be present")
```

---

## Error Messages

All helpers provide informative error messages:

```simple
# assert_eq failure shows:
# "Custom message: expected 42, got 43"

# assert_some failure shows:
# "Custom message: expected Some, got None"

# assert_called failure shows:
# "Expected 3 calls, got 1"
# [Call log with details]

# assert_fast failure shows:
# "Custom message: took 150000μs, limit was 100000μs"
```

---

## Time Units

Timing functions use microseconds (μs):

| Unit | Microseconds | Example |
|------|--------------|---------|
| 1 millisecond | 1,000 μs | `1000` |
| 10 milliseconds | 10,000 μs | `10000` |
| 100 milliseconds | 100,000 μs | `100000` |
| 1 second | 1,000,000 μs | `1000000` |

```simple
testing.assert_fast(\: operation(), 1000, "1ms limit")
testing.assert_fast(\: operation(), 10000, "10ms limit")
testing.assert_fast(\: operation(), 100000, "100ms limit")
testing.assert_fast(\: operation(), 1000000, "1 second limit")
```

---

## Tips

### ✅ Do

- Use descriptive assertion messages
- One assertion per concept when possible
- Clean up resources with `with_cleanup`
- Use mocks to isolate units
- Use `assert_some` and `assert_ok` to unwrap safely

### ❌ Don't

- Don't use vague messages like "test failed"
- Don't mix multiple unrelated assertions in one test
- Don't forget to clean up resources
- Don't use real dependencies in unit tests
- Don't manually unwrap without checking

---

## See Also

- **Full Guide:** `doc/guide/comprehensive_testing.md`
- **Benchmarking:** `doc/guide/benchmarking.md`
- **Smoke Testing:** `doc/guide/smoke_testing.md`
- **Mocking:** `doc/guide/mocking.md`
- **Examples:** `simple/std_lib/examples/testing/`

---

## Cheat Sheet Summary

```simple
import testing

# Assertions
testing.assert_eq(a, b, "msg")
testing.assert_true(cond, "msg")
testing.assert_some(opt, "msg") -> T
testing.assert_ok(res, "msg") -> T

# Timing
val (result, μs) = testing.measure_time(\: action())
val result = testing.assert_fast(\: action(), max_μs, "msg")

# Mocks
val spy = testing.create_spy("name")
testing.assert_called(spy, count)
testing.assert_called_with(spy, args)

# Collections
testing.assert_contains(list, item, "msg")
testing.assert_len(list, n, "msg")

# Fixtures
testing.with_cleanup(\: setup(), \x: teardown(x), \x: test(x))
```

---

**Happy Testing! 🎉**
