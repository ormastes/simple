# Safe Unwrap Operators Specification
*Source:* `test/feature/usage/safe_unwrap_operators_spec.spl`
**Feature IDs:** #OPERATORS-SAFE-UNWRAP  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



Safe unwrap operators provide ergonomic ways to extract values from Option<T>
and Result<T, E> types with default fallbacks or error handling. They eliminate
the need for manual pattern matching in common cases while remaining type-safe.

## Syntax

```simple
opt unwrap or: default_value              # Use default if None
opt unwrap else: \: lazy_default_expr     # Lazy evaluation of default
result unwrap or_return: default_on_err   # Early return with default
```

## Key Behaviors

- `unwrap or:` evaluates the default value immediately (eager)
- `unwrap else:` takes a closure for lazy evaluation (only called if needed)
- `unwrap or_return:` returns from the function with a default value on error
- Works with both Option<T> and Result<T, E> types
- Provides inline alternatives to verbose pattern matching
- Type-safe: never causes runtime panics

## Feature: Safe Unwrap Operators

Verifies that safe unwrap operators provide ergonomic value extraction
    from Option and Result types. Tests cover eager evaluation (`unwrap or:`),
    lazy evaluation (`unwrap else:`), and early return (`unwrap or_return:`).

### Scenario: unwrap or: with eager evaluation

| # | Example | Status |
|---|---------|--------|
| 1 | returns value when Option is Some | pass |
| 2 | returns default when Option is None | pass |
| 3 | works with Result Ok | pass |
| 4 | returns default for Result Err | pass |
| 5 | evaluates default expression | pass |
| 6 | handles complex default expressions | pass |
| 7 | works with string defaults | pass |
| 8 | preserves value type through unwrap | pass |

**Example:** returns value when Option is Some
    Given val opt: Option<i64> = Some(42)
    Given val result = opt unwrap or: 0
    Then  expect result == 42

**Example:** returns default when Option is None
    Given val opt: Option<i64> = None
    Given val result = opt unwrap or: 0
    Then  expect result == 0

**Example:** works with Result Ok
    Given val res: Result<i64, text> = Ok(42)
    Given val result = res unwrap or: 0
    Then  expect result == 42

**Example:** returns default for Result Err
    Given val res: Result<i64, text> = Err("error")
    Given val result = res unwrap or: -1
    Then  expect result == -1

**Example:** evaluates default expression
    Given val opt: Option<i64> = None
    Given val result = opt unwrap or: 10 + 5
    Then  expect result == 15

**Example:** handles complex default expressions
    Given val opt: Option<text> = None
    Given val result = opt unwrap or: "default".upper()
    Then  expect result == "DEFAULT"

**Example:** works with string defaults
    Given val opt: Option<text> = None
    Given val result = opt unwrap or: "fallback"
    Then  expect result == "fallback"

**Example:** preserves value type through unwrap
    Given val opt: Option<i64> = Some(100)
    Given val result = opt unwrap or: 0
    Then  expect result == 100

### Scenario: unwrap else: with lazy evaluation

| # | Example | Status |
|---|---------|--------|
| 1 | returns value when Option is Some without calling closure | pass |
| 2 | calls closure only when Option is None | pass |
| 3 | works with Result Ok without evaluating closure | pass |
| 4 | evaluates closure for Result Err | pass |
| 5 | closure can perform side effects | pass |
| 6 | lazy evaluation skips expensive computation when value exists | pass |

**Example:** returns value when Option is Some without calling closure
    Given val opt: Option<i64> = Some(42)
    Given var called = false
    Given val result = opt unwrap else: \:
    Then  expect result == 42
    Then  expect called == false

**Example:** calls closure only when Option is None
    Given val opt: Option<i64> = None
    Given var called = false
    Given val result = opt unwrap else: \:
    Then  expect result == 99
    Then  expect called == true

**Example:** works with Result Ok without evaluating closure
    Given val res: Result<i64, text> = Ok(42)
    Given var called = false
    Given val result = res unwrap else: \:
    Then  expect result == 42
    Then  expect called == false

**Example:** evaluates closure for Result Err
    Given val res: Result<i64, text> = Err("failed")
    Given var called = false
    Given val result = res unwrap else: \:
    Then  expect result == -1
    Then  expect called == true

**Example:** closure can perform side effects
    Given var side_effect = 0
    Given val opt: Option<i64> = None
    Given val result = opt unwrap else: \:
    Then  expect result == 42
    Then  expect side_effect == 100

**Example:** lazy evaluation skips expensive computation when value exists
    Given val opt: Option<i64> = Some(1)
    Given var expensive_called = false
    Given val result = opt unwrap else: \:
    Then  expect result == 1
    Then  expect expensive_called == false

### Scenario: unwrap or_return: with early return

| # | Example | Status |
|---|---------|--------|
| 1 | returns value when present | pass |
| 2 | returns default when None | pass |
| 3 | works with Result | pass |
| 4 | returns default for Result Err | pass |

**Example:** returns value when present
    Given val opt: Option<i64> = Some(42)
    Given val value = opt unwrap or_return: 0
    Then  expect get_value_or_early() == 43

**Example:** returns default when None
    Given val opt: Option<i64> = None
    Given val value = opt unwrap or_return: 0
    Then  expect get_value_or_early() == 0

**Example:** works with Result
    Given val res: Result<i64, text> = Ok(42)
    Given val value = res unwrap or_return: -1
    Then  expect parse_number_or_early() == 84

**Example:** returns default for Result Err
    Given val res: Result<i64, text> = Err("parse error")
    Given val value = res unwrap or_return: -1
    Then  expect parse_number_or_early() == -1

### Scenario: chaining and composition

| # | Example | Status |
|---|---------|--------|
| 1 | can chain multiple unwrap operations | pass |
| 2 | works in nested expressions | pass |

**Example:** can chain multiple unwrap operations
    Given val v1 = opt1 unwrap or: 0
    Given val v2 = opt2 unwrap or: 0
    Then  expect chain_result(Some(10), Some(20)) == 30
    Then  expect chain_result(Some(10), None) == 10
    Then  expect chain_result(None, Some(20)) == 20
    Then  expect chain_result(None, None) == 0

**Example:** works in nested expressions
    Given val opt: Option<i64> = Some(5)
    Given val result = (opt unwrap or: 0) * 2 + 10
    Then  expect result == 20

### Scenario: type safety

| # | Example | Status |
|---|---------|--------|
| 1 | preserves Option type semantics | pass |
| 2 | handles nested Option types | pass |
| 3 | preserves Result error information | pass |

**Example:** preserves Option type semantics
    Given val maybe_value: Option<text> = Some("hello")
    Given val text_result = maybe_value unwrap or: "world"
    Then  expect text_result == "hello"

**Example:** handles nested Option types
    Given val nested: Option<Option<i64>> = Some(Some(42))
    Given val inner = nested unwrap or: Some(0)
    Then  expect inner == Some(42)

**Example:** preserves Result error information
    Given val result: Result<i64, text> = Err("error message")
    Given val recovered = result unwrap or: 0
    Then  expect recovered == 0


