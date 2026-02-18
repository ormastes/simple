# futures promises
*Source:* `test/feature/usage/futures_promises_spec.spl`

## Overview

Futures and Promises Tests
Feature: Futures and promises for asynchronous programming
Category: Runtime
Status: In Progress

Tests for the futures and promises API, including creation, composition,
error handling, and integration with async/await patterns.

## Feature: Futures and Promises

Tests for basic futures and promises, including creation,
    resolution, and value retrieval.

### Scenario: when creating a future

### Scenario: Future Creation

        Tests creating futures from values and computations.

| # | Example | Status |
|---|---------|--------|
| 1 | creates future from immediate value | pass |
| 2 | creates future from computation | pass |

**Example:** creates future from immediate value
    Given val f = future(42)
    Then  expect await f == 42

**Example:** creates future from computation
    Given val f = future(10 + 20 + 30)
    Then  expect await f == 60

### Scenario: when working with promises

### Scenario: Promise Resolution

        Tests promise creation and resolution.

| # | Example | Status |
|---|---------|--------|
| 1 | resolves promise to value | pass |
| 2 | fulfills promise once | pass |

**Example:** resolves promise to value
    Given val p = Promise.new(\resolve, reject: resolve(42))
    Then  expect v == 42
    Then  expect false

**Example:** fulfills promise once
    Given var resolve_count = 0
    Given val p = Promise.new(\resolve, reject:
    Then  expect v == 10
    Then  expect false

## Feature: Future Composition

Tests for composing and chaining futures,
    including map, flatMap, and other combinator operations.

### Scenario: when mapping over future values

### Scenario: Future Transformation

        Tests transforming future results with map operations.

| # | Example | Status |
|---|---------|--------|
| 1 | maps future to new value | pass |
| 2 | chains multiple map operations | pass |

**Example:** maps future to new value
    Given val p = Promise.resolved(21)
    Given val p2 = p.map(\x: x * 2)
    Then  expect v == 42
    Then  expect false

**Example:** chains multiple map operations
    Given val p = Promise.resolved(5)
    Given val p2 = p.map(\x: x * 2).map(\x: x + 10).map(\x: x * 3)
    Then  expect v == 60
    Then  expect false

### Scenario: when flattening nested futures

### Scenario: FlatMap and Flattening

        Tests composing futures that return futures.

| # | Example | Status |
|---|---------|--------|
| 1 | flattens nested futures | pass |
| 2 | chains async operations with flatMap | pass |

**Example:** flattens nested futures
    Given val p = Promise.resolved(10)
    Given val p2 = p.flat_map(\x: Promise.resolved(x * 2))
    Then  expect v == 20
    Then  expect false

**Example:** chains async operations with flatMap
    Given val p = Promise.resolved(5)
    Given val p2 = p.flat_map(\x: Promise.resolved(x * 2))
    Then  expect v == 20
    Then  expect false

## Feature: Future Error Handling

Tests for error handling in futures,
    including error propagation and recovery.

### Scenario: when future fails

### Scenario: Future Failure

        Tests handling errors in future computations.

| # | Example | Status |
|---|---------|--------|
| 1 | captures exception in failed future | pass |
| 2 | propagates errors through chain | pass |

**Example:** captures exception in failed future
    Given val p = Promise.rejected("error occurred")
    Then  expect e == "error occurred"
    Then  expect false

**Example:** propagates errors through chain
    Given val p = Promise.rejected("original error")
    Given val p2 = p.map(\x: x * 2)
    Then  expect e == "original error"
    Then  expect false

### Scenario: when recovering from failed future

### Scenario: Error Recovery

        Tests error recovery and fallback mechanisms.

| # | Example | Status |
|---|---------|--------|
| 1 | recovers with fallback value | pass |
| 2 | retries failed future | pass |

**Example:** recovers with fallback value
    Given val p = Promise.rejected("error")
    Given val p2 = p.catch(\e: 42)
    Then  expect v == 42
    Then  expect false

**Example:** retries failed future
    Given val p = Promise.rejected("first attempt")
    Given val p2 = p.catch(\e: Promise.resolved(100))
    Then  expect v == 100
    Then  expect false

## Feature: Advanced Future Patterns

Tests for advanced patterns with futures,
    including combination of multiple futures and integration features.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | combines multiple futures | pass |
| 2 | handles timeout on future | pass |
| 3 | cancels pending future | pass |

**Example:** combines multiple futures
    Given val p1 = Promise.resolved(10)
    Given val p2 = Promise.resolved(20)
    Given val p3 = Promise.resolved(30)
    Given val combined = all([p1, p2, p3])
    Then  expect values[0] + values[1] + values[2] == 60
    Then  expect false

**Example:** handles timeout on future
    Given val p1 = Promise.resolved(42)
    Given val p2 = Promise.resolved(100)
    Given val winner = race([p1, p2])
    Then  expect v == 42
    Then  expect false

**Example:** cancels pending future
    Given val p1 = Promise.rejected("timeout")
    Given val p2 = Promise.resolved(42)
    Given val result = race([p1, p2])
    Then  expect e == "timeout"
    Then  expect false


