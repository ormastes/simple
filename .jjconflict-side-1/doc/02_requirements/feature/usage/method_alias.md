# Method Alias Forwarding Specification
*Source:* `test/feature/usage/method_alias_spec.spl`
**Feature IDs:** #FWD-002  |  **Category:** Syntax  |  **Status:** In Progress

## Overview



## Overview

Tests that `alias fn` and `alias me` in class bodies desugar into
correct forwarding methods. The desugar transforms:
  `alias fn len = inner.len`       -> `fn len(): self.inner.len()`
  `alias fn push(item) = inner.push` -> `fn push(item): self.inner.push(item)`
  `alias me increment = inner.increment` -> `me increment(): self.inner.increment()`

These tests verify the generated delegation patterns work correctly
by writing the equivalent hand-expanded code.

## Feature: method alias forwarding

### Scenario: immutable forwarding (alias fn)

| # | Example | Status |
|---|---------|--------|
| 1 | forwards no-arg method | pass |
| 2 | forwards method with argument | pass |
| 3 | forwards zero value correctly | pass |

**Example:** forwards no-arg method
    Given val w = make_wrapper(42)
    Then  expect(w.get_count()).to_equal(42)

**Example:** forwards method with argument
    Given val w = make_wrapper(10)
    Then  expect(w.get_count_plus(5)).to_equal(15)

**Example:** forwards zero value correctly
    Given val w = make_wrapper(0)
    Then  expect(w.get_count()).to_equal(0)

### Scenario: mutable forwarding (alias me)

| # | Example | Status |
|---|---------|--------|
| 1 | forwards no-arg mutable method | pass |
| 2 | forwards mutable method with argument | pass |
| 3 | chains multiple mutable forwards | pass |

**Example:** forwards no-arg mutable method
    Given var w = make_wrapper(5)
    Then  expect(w.get_count()).to_equal(6)

**Example:** forwards mutable method with argument
    Given var w = make_wrapper(10)
    Then  expect(w.get_count()).to_equal(17)

**Example:** chains multiple mutable forwards
    Given var w = make_wrapper(0)
    Then  expect(w.get_count()).to_equal(12)

### Scenario: forwarding preserves inner state

| # | Example | Status |
|---|---------|--------|
| 1 | reads after mutation reflect changes | pass |

**Example:** reads after mutation reflect changes
    Given var w = make_wrapper(100)
    Given val result = w.get_count_plus(25)
    Then  expect(result).to_equal(75)


