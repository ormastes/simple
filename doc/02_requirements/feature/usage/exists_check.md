# Existence Check Operator (.?) Specification
*Source:* `test/feature/usage/exists_check_spec.spl`
**Feature IDs:** #2100  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



The `.?` operator checks if a value is "present" (non-nil AND non-empty).

## Feature: Existence Check Operator .?

Verifies the existence check operator `.?` that tests whether a value is
    "present" (non-nil AND non-empty). This operator provides a concise way to
    check Option<T> for Some, collections for non-emptiness, and strings for
    non-empty content. Primitives always return true since they always exist.
    The operator integrates with no-paren method calls for idiomatic patterns
    like `list.first.?` and `str.trim.?`.

### Scenario: Option type

| # | Example | Status |
|---|---------|--------|
| 1 | returns true for Some | pass |
| 2 | returns true for Some(0) | pass |
| 3 | returns false for None | pass |

**Example:** returns true for Some
    Given val some_val: Option<i32> = Some(42)
    Then  expect some_val.? == true

**Example:** returns true for Some(0)
    Given val some_zero: Option<i32> = Some(0)
    Then  expect some_zero.? == true

**Example:** returns false for None
    Given val none_val: Option<i32> = None
    Then  expect none_val.? == false

### Scenario: List type

| # | Example | Status |
|---|---------|--------|
| 1 | returns false for empty list | pass |
| 2 | returns true for non-empty list | pass |

**Example:** returns false for empty list
    Given val empty: List<i32> = []
    Then  expect empty.? == false

**Example:** returns true for non-empty list
    Given val items = [1, 2, 3]
    Then  expect items.? == true

### Scenario: Dict type

| # | Example | Status |
|---|---------|--------|
| 1 | returns false for empty dict | pass |
| 2 | returns true for non-empty dict | pass |

**Example:** returns false for empty dict
    Given val empty: Dict<text, i32> = {}
    Then  expect empty.? == false

**Example:** returns true for non-empty dict
    Given val items = {"a": 1}
    Then  expect items.? == true

### Scenario: String type

| # | Example | Status |
|---|---------|--------|
| 1 | returns false for empty string | pass |
| 2 | returns true for non-empty string | pass |

**Example:** returns false for empty string
    Given val empty = ""
    Then  expect empty.? == false

**Example:** returns true for non-empty string
    Given val s = "hello"
    Then  expect s.? == true

### Scenario: Primitive types

| # | Example | Status |
|---|---------|--------|
| 1 | returns true for positive number | pass |
| 2 | returns true for zero | pass |
| 3 | returns true for false | pass |

**Example:** returns true for positive number
    Given val num = 42
    Then  expect num.? == true

**Example:** returns true for zero
    Given val zero = 0
    Then  expect zero.? == true

**Example:** returns true for false
    Given val flag = false
    Then  expect flag.? == true

### Scenario: with no-paren method calls

| # | Example | Status |
|---|---------|--------|
| 1 | works with list.first.? | pass |
| 2 | returns false for empty list.first.? | pass |
| 3 | works with string.trim.? | pass |
| 4 | works with chained no-paren methods | pass |
| 5 | returns false for empty result | pass |

**Example:** works with list.first.?
    Given val items = [1, 2, 3]
    Then  expect items.first.? == true

**Example:** returns false for empty list.first.?
    Given val empty: List<i32> = []
    Then  expect empty.first.? == false

**Example:** works with string.trim.?
    Given val s = "  hello  "
    Then  expect s.trim.? == true

**Example:** works with chained no-paren methods
    Given val s = "  HELLO  "
    Then  expect s.trim.lower.? == true

**Example:** returns false for empty result
    Given val empty = ""
    Then  expect empty.trim.? == false


