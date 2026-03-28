# freeze unfreeze
*Source:* `test/feature/usage/freeze_unfreeze_spec.spl`

## Overview

Freeze and Unfreeze - Comprehensive SSpec Tests
Testing freeze() function for creating immutable collections

Category: Collections
Status: Implemented

## Feature: Freeze and Unfreeze

### Scenario: Freeze Function

| # | Example | Status |
|---|---------|--------|
| 1 | freezes mutable array | pass |
| 2 | freezes mutable dict | pass |
| 3 | is idempotent | pass |
| 4 | freezes empty array | pass |
| 5 | freezes empty dict | pass |

**Example:** freezes mutable array
    Given var arr = [1, 2, 3]
    Given val frozen = freeze(arr)
    Then  expect frozen[0] == 1
    Then  expect frozen.len() == 3

**Example:** freezes mutable dict
    Given var dict = {"a": 1}
    Given val frozen = freeze(dict)
    Then  expect frozen["a"] == 1

**Example:** is idempotent
    Given val arr = freeze([1, 2, 3])
    Given val frozen_again = freeze(arr)
    Then  expect frozen_again[0] == arr[0]
    Then  expect frozen_again.len() == arr.len()

**Example:** freezes empty array
    Given val frozen = freeze([])
    Then  expect frozen.len() == 0

**Example:** freezes empty dict
    Given val frozen = freeze({})
    Then  expect frozen.len() == 0

### Scenario: Frozen Array Operations

| # | Example | Status |
|---|---------|--------|
| 1 | allows reads on frozen array | pass |
| 2 | allows len on frozen array | pass |
| 3 | allows iteration on frozen array | pass |
| 4 | allows first and last on frozen array | pass |
| 5 | allows negative indexing on frozen array | pass |

**Example:** allows reads on frozen array
    Given val frozen = freeze([1, 2, 3])
    Then  expect frozen[0] == 1
    Then  expect frozen[2] == 3

**Example:** allows len on frozen array
    Given val frozen = freeze([1, 2, 3])
    Then  expect frozen.len() == 3

**Example:** allows iteration on frozen array
    Given val frozen = freeze([1, 2, 3])
    Given var sum = 0
    Then  expect sum == 6

**Example:** allows first and last on frozen array
    Given val frozen = freeze([1, 2, 3])
    Then  expect frozen.first() == 1
    Then  expect frozen.last() == 3

**Example:** allows negative indexing on frozen array
    Given val frozen = freeze([1, 2, 3])
    Then  expect frozen[-1] == 3
    Then  expect frozen[-2] == 2

### Scenario: Functional Operations on Frozen

| # | Example | Status |
|---|---------|--------|
| 1 | allows map on frozen array | pass |
| 2 | allows filter on frozen array | pass |
| 3 | allows reduce on frozen array | pass |
| 4 | allows contains on frozen array | pass |

**Example:** allows map on frozen array
    Given val frozen = freeze([1, 2, 3])
    Given val doubled = frozen.map(\x: x * 2)
    Then  expect doubled[0] == 2
    Then  expect doubled[1] == 4
    Then  expect doubled[2] == 6

**Example:** allows filter on frozen array
    Given val frozen = freeze([1, 2, 3, 4, 5])
    Given val evens = frozen.filter(\x: x % 2 == 0)
    Then  expect evens.len() == 2
    Then  expect evens[0] == 2
    Then  expect evens[1] == 4

**Example:** allows reduce on frozen array
    Given val frozen = freeze([1, 2, 3, 4])
    Given val sum = frozen.reduce(0, \acc, x: acc + x)
    Then  expect sum == 10

**Example:** allows contains on frozen array
    Given val frozen = freeze([1, 2, 3])
    Then  expect frozen.contains(2)
    Then  expect not frozen.contains(5)

### Scenario: Frozen Dict Operations

| # | Example | Status |
|---|---------|--------|
| 1 | allows reads on frozen dict | pass |
| 2 | allows len on frozen dict | pass |
| 3 | allows keys on frozen dict | pass |
| 4 | allows values on frozen dict | pass |
| 5 | allows contains_key on frozen dict | pass |

**Example:** allows reads on frozen dict
    Given val frozen = freeze({"a": 1, "b": 2})
    Then  expect frozen["a"] == 1
    Then  expect frozen["b"] == 2

**Example:** allows len on frozen dict
    Given val frozen = freeze({"a": 1, "b": 2})
    Then  expect frozen.len() == 2

**Example:** allows keys on frozen dict
    Given val frozen = freeze({"a": 1, "b": 2})
    Given val keys = frozen.keys()
    Then  expect keys.len() == 2

**Example:** allows values on frozen dict
    Given val frozen = freeze({"a": 1, "b": 2})
    Given val values = frozen.values()
    Then  expect values.len() == 2

**Example:** allows contains_key on frozen dict
    Given val frozen = freeze({"a": 1})
    Then  expect frozen.contains_key("a")
    Then  expect not frozen.contains_key("b")

### Scenario: Type Behavior

| # | Example | Status |
|---|---------|--------|
| 1 | treats frozen arrays as arrays | pass |
| 2 | treats frozen dicts as dicts | pass |

**Example:** treats frozen arrays as arrays
    Given val frozen = freeze([1, 2, 3])
    Then  expect frozen.len() == 3
    Then  expect frozen[0] == 1

**Example:** treats frozen dicts as dicts
    Given val frozen = freeze({"a": 1})
    Then  expect frozen["a"] == 1


