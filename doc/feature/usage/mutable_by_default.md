# mutable by default
*Source:* `test/feature/usage/mutable_by_default_spec.spl`

## Overview

Mutable Collections by Default - Comprehensive SSpec Tests
Decision #3: Collections are mutable by default (like Python, JS, Java)

Category: Collections
Status: Implemented

## Feature: Mutable Collections by Default

### Scenario: Array Mutability

| # | Example | Status |
|---|---------|--------|
| 1 | allows push on default arrays | pass |
| 2 | allows pop on default arrays | pass |
| 3 | allows multiple pops | pass |
| 4 | allows insert on default arrays | pass |
| 5 | allows insert at beginning | pass |
| 6 | allows insert at end | pass |
| 7 | allows remove on default arrays | pass |
| 8 | allows remove first element | pass |
| 9 | allows remove last element | pass |
| 10 | allows clear on default arrays | pass |
| 11 | allows indexing assignment | pass |
| 12 | allows indexing assignment at boundaries | pass |

**Example:** allows push on default arrays
    Given var arr = [1, 2, 3]
    Then  expect arr.len() == 4
    Then  expect arr[3] == 4

**Example:** allows pop on default arrays
    Given var arr = [1, 2, 3]
    Given val last = arr.pop()
    Then  expect last == 3
    Then  expect arr.len() == 2

**Example:** allows multiple pops
    Given var arr = [1, 2, 3, 4, 5]
    Then  expect arr.len() == 3
    Then  expect arr[2] == 3

**Example:** allows insert on default arrays
    Given var arr = [1, 3]
    Then  expect arr.len() == 3
    Then  expect arr[1] == 2

**Example:** allows insert at beginning
    Given var arr = [2, 3]
    Then  expect arr[0] == 1

**Example:** allows insert at end
    Given var arr = [1, 2]
    Then  expect arr[2] == 3

**Example:** allows remove on default arrays
    Given var arr = [1, 2, 3]
    Given val removed = arr.remove(1)
    Then  expect removed == 2
    Then  expect arr.len() == 2

**Example:** allows remove first element
    Given var arr = [1, 2, 3]
    Given val removed = arr.remove(0)
    Then  expect removed == 1
    Then  expect arr[0] == 2

**Example:** allows remove last element
    Given var arr = [1, 2, 3]
    Given val removed = arr.remove(2)
    Then  expect removed == 3
    Then  expect arr.len() == 2

**Example:** allows clear on default arrays
    Given var arr = [1, 2, 3]
    Then  expect arr.len() == 0

**Example:** allows indexing assignment
    Given var arr = [1, 2, 3]
    Then  expect arr[1] == 10

**Example:** allows indexing assignment at boundaries
    Given var arr = [1, 2, 3]
    Then  expect arr[0] == 10
    Then  expect arr[2] == 30

### Scenario: Dict Mutability

| # | Example | Status |
|---|---------|--------|
| 1 | allows insert on default dicts | pass |
| 2 | allows update existing key | pass |
| 3 | allows remove on default dicts | pass |
| 4 | allows clear on default dicts | pass |

**Example:** allows insert on default dicts
    Given var dict = {"a": 1}
    Then  expect dict["b"] == 2

**Example:** allows update existing key
    Given var dict = {"a": 1}
    Then  expect dict["a"] == 10

**Example:** allows remove on default dicts
    Given var dict = {"a": 1, "b": 2}
    Then  expect dict.len() == 1

**Example:** allows clear on default dicts
    Given var dict = {"a": 1, "b": 2}
    Then  expect dict.len() == 0

### Scenario: var binding with mutable collection

| # | Example | Status |
|---|---------|--------|
| 1 | allows mutation with var binding | pass |
| 2 | allows pop with var binding | pass |
| 3 | works with dict and val binding | pass |

**Example:** allows mutation with var binding
    Given var arr = [1, 2, 3]
    Then  expect arr.len() == 4
    Then  expect arr[3] == 4

**Example:** allows pop with var binding
    Given var arr = [1, 2, 3]
    Then  expect arr.len() == 2

**Example:** works with dict and val binding
    Given val dict = {"a": 1}
    Then  expect dict["b"] == 2

### Scenario: Sequential operations

| # | Example | Status |
|---|---------|--------|
| 1 | handles sequential borrows | pass |
| 2 | allows read after write | pass |

**Example:** handles sequential borrows
    Given var arr = [1, 2, 3]
    Given val len = arr.len()
    Then  expect len == 3
    Then  expect arr.len() == 4

**Example:** allows read after write
    Given var arr = [1, 2, 3]
    Given val last = arr[3]
    Then  expect last == 4

### Scenario: Empty collection mutations

| # | Example | Status |
|---|---------|--------|
| 1 | allows push to empty array | pass |
| 2 | handles pop from singleton | pass |
| 3 | allows insert into empty dict | pass |

**Example:** allows push to empty array
    Given var arr = []
    Then  expect arr.len() == 1
    Then  expect arr[0] == 1

**Example:** handles pop from singleton
    Given var arr = [1]
    Given val elem = arr.pop()
    Then  expect elem == 1
    Then  expect arr.len() == 0

**Example:** allows insert into empty dict
    Given var dict = {}
    Then  expect dict["key"] == "value"


