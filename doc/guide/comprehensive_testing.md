# Comprehensive Testing Guide for Simple
**A Complete Guide to Testing in Simple Language**

## Table of Contents

1. [Introduction](#introduction)
2. [Quick Start](#quick-start)
3. [Testing Libraries Overview](#testing-libraries-overview)
4. [Test Helpers Reference](#test-helpers-reference)
5. [Common Testing Patterns](#common-testing-patterns)
6. [Real-World Examples](#real-world-examples)
7. [Best Practices](#best-practices)
8. [Troubleshooting](#troubleshooting)

## Introduction

Simple provides a comprehensive testing ecosystem with four main components:

1. **Test Helpers** - Assertion and utility functions for writing tests
2. **Benchmarking** - Statistical performance measurement
3. **Smoke Testing** - Post-deployment verification
4. **Mocking** - Test doubles and call verification

This guide shows you how to use these libraries together effectively.

## Quick Start

### Installation

All testing libraries are part of the Simple standard library:

```simple
import testing                    # All testing utilities
import testing.benchmark as bench # Benchmarking
import testing.deployment as smoke # Smoke testing
import testing.mock as mock       # Mocking
```

### Your First Test

```simple
import testing

describe "Calculator":
    context "Addition":
        skip "adds two numbers correctly":
            val result = 2 + 2
            testing.assert_eq(result, 4, "2 + 2 should equal 4")
```

### Running Tests

```bash
# Run all tests in a file
simple test test/calculator_spec.spl

# Run specific context
simple test test/calculator_spec.spl --filter "Addition"
```

## Testing Libraries Overview

### Test Helpers

**Purpose:** Common assertions and utilities for writing tests

**When to use:**
- Writing unit tests
- Asserting conditions
- Measuring execution time
- Setting up test fixtures

**Example:**
```simple
import testing

val result = Some(42)
val value = testing.assert_some(result, "Should return a value")
testing.assert_eq(value, 42, "Value should be 42")
```

### Benchmarking

**Purpose:** Measure and compare performance

**When to use:**
- Optimizing algorithms
- Comparing implementations
- Regression testing performance
- Establishing performance baselines

**Example:**
```simple
import testing.benchmark as bench

val stats = bench.benchmark_default("quicksort", \:
    quicksort(data)
)
print stats.summary()
```

### Smoke Testing

**Purpose:** Post-deployment verification

**When to use:**
- After deployments
- Health checks
- Integration testing
- API verification

**Example:**
```simple
import testing.deployment as smoke

val suite = smoke.SmokeTestSuite.new_default()
    .test("API responds", \: http.get("/health").status == 200)
    .test("Database connected", \: db.ping())

val results = suite.run()
```

### Mocking

**Purpose:** Create test doubles and verify interactions

**When to use:**
- Testing with external dependencies
- Verifying call patterns
- Isolating units under test
- Simulating different scenarios

**Example:**
```simple
import testing.mock as mock

val db_mock = mock.create_mock("database")
db_mock.record_call(["save", "user123"])

testing.assert_true(db_mock.was_called(), "Database should be called")
```

## Test Helpers Reference

### Assertion Helpers

#### Equality Assertions

```simple
testing.assert_eq(actual, expected, "message")
testing.assert_ne(actual, unexpected, "message")
```

**Example:**
```simple
val result = calculate_total([10, 20, 30])
testing.assert_eq(result, 60, "Total should be 60")
```

#### Boolean Assertions

```simple
testing.assert_true(condition, "message")
testing.assert_false(condition, "message")
```

**Example:**
```simple
val user = User.new("Alice")
testing.assert_true(user.is_valid(), "User should be valid")
testing.assert_false(user.is_deleted(), "User should not be deleted")
```

#### Option Assertions

```simple
val value = testing.assert_some(option, "message")  // Returns unwrapped value
testing.assert_none(option, "message")
```

**Example:**
```simple
val user = find_user("user123")
val u = testing.assert_some(user, "User should exist")
testing.assert_eq(u.name, "Alice", "User name should be Alice")
```

#### Result Assertions

```simple
val value = testing.assert_ok(result, "message")  // Returns unwrapped value
val error = testing.assert_err(result, "message") // Returns error value
```

**Example:**
```simple
val result = load_config()
val config = testing.assert_ok(result, "Config should load successfully")
testing.assert_eq(config.version, "1.0", "Config version should be 1.0")
```

### Timing Helpers

#### Measure Execution Time

```simple
val (result, elapsed_micros) = testing.measure_time(\:
    expensive_operation()
)
print "Took {elapsed_micros} microseconds"
```

#### Assert Performance Requirements

```simple
val result = testing.assert_fast(
    \: query_database(),
    100000,  // 100ms limit
    "Query should complete in 100ms"
)
```

**Example:**
```simple
val result = testing.assert_fast(
    \:
        var sum = 0
        for i in 0..1000:
            sum = sum + i
        sum
    ,
    50000,  // 50ms limit
    "Loop should be fast"
)
testing.assert_eq(result, 499500, "Sum should be correct")
```

### Mock Helpers

#### Create and Use Spies

```simple
val spy = testing.create_spy("function_name")
spy.record_call(["arg1", "arg2"])

testing.assert_called(spy, 3)  // Called exactly 3 times
testing.assert_called_with(spy, ["arg1", "arg2"])
testing.assert_not_called(spy)
```

**Example:**
```simple
val save_spy = testing.create_spy("save_user")

// Use in code
save_spy.record_call(["user123", "Alice"])
save_spy.record_call(["user456", "Bob"])

// Verify
testing.assert_called(save_spy, 2)
testing.assert_called_with(save_spy, ["user123", "Alice"])
```

### Collection Helpers

```simple
testing.assert_contains(list, item, "message")
testing.assert_not_contains(list, item, "message")
testing.assert_empty(list, "message")
testing.assert_len(list, expected_length, "message")
```

**Example:**
```simple
val users = ["Alice", "Bob", "Charlie"]

testing.assert_len(users, 3, "Should have 3 users")
testing.assert_contains(users, "Alice", "Should contain Alice")
testing.assert_not_contains(users, "David", "Should not contain David")
```

### Fixture Helpers

#### Setup and Teardown

```simple
testing.with_cleanup(
    \: create_temp_file(),    // Setup
    \file: delete_file(file),  // Teardown
    \file: test_operations(file) // Test
)
```

**Example:**
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
        val loaded = db.load("Alice")
        testing.assert_some(loaded, "User should be loaded")
)
```

#### Timeout Protection

```simple
val result = testing.with_timeout(
    \: potentially_slow_operation(),
    5.0,  // 5 second timeout
    "Operation timed out"
)
```

## Common Testing Patterns

### Pattern 1: Unit Test with Assertions

```simple
import testing

describe "User Registration":
    context "Valid input":
        skip "creates user successfully":
            val user = User.new("alice@example.com", "Alice")

            testing.assert_true(user.is_valid(), "User should be valid")
            testing.assert_eq(user.email, "alice@example.com", "Email should match")
            testing.assert_eq(user.name, "Alice", "Name should match")
```

### Pattern 2: Testing with Mocks

```simple
import testing
import testing.mock as mock

describe "User Service":
    context "Save user":
        skip "calls database correctly":
            val db_mock = mock.create_mock("database")
            val service = UserService(db: db_mock)

            service.save_user("user123", "Alice")

            testing.assert_called(db_mock, 1)
            testing.assert_called_with(db_mock, ["save", "user123", "Alice"])
```

### Pattern 3: Performance Testing

```simple
import testing
import testing.benchmark as bench

describe "Sorting Performance":
    context "Large dataset":
        skip "quicksort is fast enough":
            val data = generate_random_data(10000)

            val result = testing.assert_fast(
                \: quicksort(data),
                500000,  // 500ms limit
                "Quicksort should complete in 500ms"
            )

            testing.assert_eq(result.len(), 10000, "All items should be present")
```

### Pattern 4: Integration Testing with Smoke Tests

```simple
import testing.deployment as smoke

describe "API Integration":
    context "Post-deployment":
        skip "all endpoints respond":
            val suite = smoke.SmokeTestSuite.new_default()
                .test("Homepage", \: http.get("/").status == 200)
                .test("API health", \: http.get("/api/health").status == 200)
                .test("Database", \: db.ping())

            val results = suite.run()

            if not suite.all_passed(results):
                panic("Integration tests failed!")
```

### Pattern 5: Testing with Fixtures

```simple
import testing

describe "File Operations":
    context "With temporary file":
        skip "reads and writes correctly":
            testing.with_cleanup(
                \:
                    val file = create_temp_file()
                    write_file(file, "test data")
                    file
                ,
                \file:
                    delete_file(file)
                ,
                \file:
                    val content = read_file(file)
                    testing.assert_eq(content, "test data", "Content should match")
            )
```

### Pattern 6: Combining Multiple Libraries

```simple
import testing
import testing.benchmark as bench
import testing.mock as mock

describe "Optimized User Service":
    context "Performance with caching":
        skip "cache improves lookup speed":
            // Setup mocks
            val db_mock = mock.create_mock("database")
            val cache_mock = mock.create_mock("cache")

            val service = UserService(
                db: db_mock,
                cache: cache_mock
            )

            // Benchmark without cache
            cache_mock.set_return_values(["None"])  // Cache miss
            val (result1, time1) = testing.measure_time(\:
                service.get_user("user123")
            )

            // Benchmark with cache
            cache_mock.set_return_values(["Alice"])  // Cache hit
            val (result2, time2) = testing.measure_time(\:
                service.get_user("user123")
            )

            // Verify cache is faster
            testing.assert_true(time2 < time1, "Cache should be faster")

            // Verify cache was used
            testing.assert_called(cache_mock, 2)
```

## Real-World Examples

### Example 1: E-commerce Order Service

```simple
import testing
import testing.mock as mock

describe "Order Service":
    context "Place order":
        skip "processes order correctly":
            // Setup mocks
            val payment_mock = mock.create_mock("payment")
            val inventory_mock = mock.create_mock("inventory")
            val email_mock = mock.create_mock("email")

            payment_mock.set_return_values(["success"])
            inventory_mock.set_return_values(["available"])

            val service = OrderService(
                payment: payment_mock,
                inventory: inventory_mock,
                email: email_mock
            )

            // Place order
            val order = Order.new("user123", ["item1", "item2"], 99.99)
            val result = service.place_order(order)

            // Verify result
            val order_id = testing.assert_ok(result, "Order should succeed")

            // Verify interactions
            testing.assert_called(inventory_mock, 1)
            testing.assert_called(payment_mock, 1)
            testing.assert_called(email_mock, 1)

            // Verify call order and arguments
            testing.assert_called_with(payment_mock, ["charge", "user123", "99.99"])
            testing.assert_called_with(email_mock, ["send_confirmation", "user123", order_id])
```

### Example 2: API Performance Testing

```simple
import testing.benchmark as bench
import map

describe "API Performance":
    context "Response times":
        skip "all endpoints meet SLA":
            val endpoints = Map.new()

            endpoints.insert("GET /users", \: api.get("/users"))
            endpoints.insert("GET /products", \: api.get("/products"))
            endpoints.insert("POST /orders", \: api.post("/orders", test_order))

            val results = bench.compare_default(endpoints)

            // Verify all endpoints meet 100ms SLA
            for (endpoint, stats) in results.entries():
                val mean_ms = stats.mean_ns / 1_000_000.0
                testing.assert_true(
                    mean_ms < 100.0,
                    "{endpoint} exceeded 100ms SLA (took {mean_ms}ms)"
                )
```

### Example 3: Database Integration with Cleanup

```simple
import testing

describe "User Repository":
    context "CRUD operations":
        skip "saves and loads users":
            testing.with_cleanup(
                // Setup: Create test database
                \:
                    val db = Database.connect("test.db")
                    db.migrate()
                    db
                ,
                // Teardown: Clean up database
                \db:
                    db.disconnect()
                    delete_file("test.db")
                ,
                // Test: Verify CRUD operations
                \db:
                    val repo = UserRepository.new(db)

                    // Create
                    val user = User.new("alice@example.com", "Alice")
                    val id = testing.assert_ok(
                        repo.save(user),
                        "Save should succeed"
                    )

                    // Read
                    val loaded = testing.assert_some(
                        repo.find_by_id(id),
                        "User should be found"
                    )
                    testing.assert_eq(loaded.email, user.email, "Email should match")

                    // Update
                    loaded.name = "Alice Smith"
                    testing.assert_ok(repo.update(loaded), "Update should succeed")

                    // Delete
                    testing.assert_ok(repo.delete(id), "Delete should succeed")
                    testing.assert_none(repo.find_by_id(id), "User should be deleted")
            )
```

### Example 4: Deployment Verification

```simple
import testing.deployment as smoke
import testing

describe "Production Deployment":
    context "Health checks":
        skip "all services are healthy":
            val suite = smoke.SmokeTestSuite.new_default()
                // Web server
                .test("Web responds", \:
                    http.get("https://example.com").status == 200
                )

                // API
                .test("API health", \:
                    val resp = http.get("https://api.example.com/health")
                    resp.status == 200 and resp.body.contains("ok")
                )

                // Database
                .test("Database connected", \:
                    db.connect("prod.db").ping()
                )

                // Cache
                .test("Redis responds", \:
                    redis.ping() == "PONG"
                )

                // Message queue
                .test("Queue accessible", \:
                    queue.stats().is_some()
                )

            val results = suite.run()

            // Report results
            for result in results:
                print result.format()

            // Rollback if any test failed
            if not suite.all_passed(results):
                print "❌ Deployment verification failed!"
                rollback_deployment()
                panic("Rolled back deployment due to health check failures")

            print "✅ All health checks passed!"
```

## Best Practices

### 1. Use Descriptive Test Names

**Good:**
```simple
skip "returns error when user not found":
    // ...
```

**Bad:**
```simple
skip "test1":
    // ...
```

### 2. One Assertion Per Concept

**Good:**
```simple
skip "creates valid user":
    val user = User.new("alice@example.com", "Alice")
    testing.assert_true(user.is_valid(), "User should be valid")

skip "sets user email correctly":
    val user = User.new("alice@example.com", "Alice")
    testing.assert_eq(user.email, "alice@example.com", "Email should match")
```

**Better than:**
```simple
skip "creates user":
    val user = User.new("alice@example.com", "Alice")
    testing.assert_true(user.is_valid(), "User should be valid")
    testing.assert_eq(user.email, "alice@example.com", "Email should match")
    testing.assert_eq(user.name, "Alice", "Name should match")
```

### 3. Use Helpers for Common Patterns

**Before:**
```simple
if result.is_none():
    panic("Expected Some, got None")
val value = result.unwrap()
```

**After:**
```simple
val value = testing.assert_some(result, "Should return value")
```

### 4. Clean Up Resources

**Always use fixtures for resources:**
```simple
testing.with_cleanup(
    \: create_resource(),
    \r: cleanup_resource(r),
    \r: test_resource(r)
)
```

### 5. Use Mocks to Isolate Units

**Good - Isolated:**
```simple
val db_mock = mock.create_mock("database")
val service = UserService(db: db_mock)
// Test only UserService logic
```

**Bad - Integration test disguised as unit test:**
```simple
val db = Database.connect("test.db")
val service = UserService(db: db)
// Tests both UserService and Database
```

### 6. Benchmark Real-World Scenarios

**Good:**
```simple
val data = load_production_dataset()  // Realistic data
val stats = bench.benchmark_default("query", \: query(data))
```

**Bad:**
```simple
val data = [1, 2, 3]  // Trivial data
val stats = bench.benchmark_default("query", \: query(data))
```

### 7. Fail Fast in Smoke Tests

```simple
val suite = smoke.SmokeTestSuite.new(
    smoke.SmokeTestConfig(
        timeout_secs: 5.0,
        retry_attempts: 2,
        retry_delay_secs: 1.0,
        fail_fast: true  // Stop on first failure
    )
)
```

### 8. Provide Meaningful Error Messages

**Good:**
```simple
testing.assert_eq(
    result,
    expected,
    "User service should return correct user data for ID {user_id}"
)
```

**Bad:**
```simple
testing.assert_eq(result, expected, "assertion failed")
```

## Troubleshooting

### Problem: Tests are slow

**Solution 1:** Use smaller datasets
```simple
// Instead of:
val data = generate_data(10000)

// Use:
val data = generate_data(100)
```

**Solution 2:** Mock expensive operations
```simple
val db_mock = mock.create_mock("database")
db_mock.set_return_values(["cached_result"])
```

**Solution 3:** Skip slow tests during development
```simple
skip "slow integration test":  // Will be skipped
    // ...
```

### Problem: Mocks not working as expected

**Check 1:** Verify you're recording calls
```simple
val mock_fn = mock.create_mock("test")
mock_fn.record_call(["arg1"])  // Don't forget this!
```

**Check 2:** Check return value setup
```simple
val mock_fn = mock.create_mock("test")
mock_fn.set_return_values(["value1", "value2"])
val v1 = mock_fn.next_return_value()  // Returns Some("value1")
val v2 = mock_fn.next_return_value()  // Returns Some("value2")
val v3 = mock_fn.next_return_value()  // Returns None (exhausted)
```

**Check 3:** Arguments are stored as strings
```simple
// When recording:
mock_fn.record_call(["123", "Alice"])  // Use strings

// When verifying:
testing.assert_called_with(mock_fn, ["123", "Alice"])
```

### Problem: Benchmarks show high variance

**Solution 1:** Increase sample size
```simple
val config = bench.BenchmarkConfig(
    warmup_iterations: 10,
    measurement_iterations: 100,
    sample_size: 1000,  // More samples
    outlier_threshold: 2.0
)
```

**Solution 2:** Add warmup iterations
```simple
val config = bench.BenchmarkConfig(
    warmup_iterations: 50,  // More warmup
    measurement_iterations: 100,
    sample_size: 500,
    outlier_threshold: 2.0
)
```

### Problem: Smoke tests timing out

**Solution 1:** Increase timeout
```simple
val config = smoke.SmokeTestConfig(
    timeout_secs: 30.0,  // Increase from default 10s
    retry_attempts: 3,
    retry_delay_secs: 2.0,
    fail_fast: false
)
```

**Solution 2:** Add retry logic
```simple
val config = smoke.SmokeTestConfig(
    timeout_secs: 10.0,
    retry_attempts: 5,  // Retry more times
    retry_delay_secs: 3.0,  // Wait longer between retries
    fail_fast: false
)
```

### Problem: Fixtures not cleaning up

**Solution:** Always use with_cleanup
```simple
testing.with_cleanup(
    \: create_resource(),
    \r:
        // Cleanup happens even if test fails
        cleanup_resource(r)
    ,
    \r: test_resource(r)
)
```

## Next Steps

### Learn More

- **Benchmarking Guide:** `doc/guide/benchmarking.md`
- **Smoke Testing Guide:** `doc/guide/smoke_testing.md`
- **Mocking Guide:** `doc/guide/mocking.md`

### Examples

- **Integration Example:** `simple/std_lib/examples/testing/integration_example.spl`
- **Benchmark Examples:** `simple/std_lib/examples/benchmarks/stdlib_data_structures.spl`
- **Individual examples:** `simple/std_lib/examples/testing/`

### Test Specifications

See `simple/std_lib/test/unit/testing/` for comprehensive test examples

---

**Happy Testing! 🎉**
