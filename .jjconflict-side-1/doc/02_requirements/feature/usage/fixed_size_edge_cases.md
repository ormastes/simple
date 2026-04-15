# fixed size edge cases
*Source:* `test/feature/usage/fixed_size_edge_cases_spec.spl`

## Overview

Fixed-Size Array Edge Cases - Comprehensive SSpec Tests

Category: Collections
Status: Implemented (Part 2/2)

## Feature: Fixed-Size Array Edge Cases

### Scenario: Size Zero

| # | Example | Status |
|---|---------|--------|
| 1 | allows size-zero arrays | pass |
| 2 | iterates over size-zero arrays | pass |

**Example:** allows size-zero arrays
    Given val empty: [i64; 0] = []
    Then  expect empty.len() == 0

**Example:** iterates over size-zero arrays
    Given val empty: [i64; 0] = []
    Given var count = 0
    Then  expect count == 0

### Scenario: Negative Indexing

| # | Example | Status |
|---|---------|--------|
| 1 | supports negative indices | pass |

**Example:** supports negative indices
    Given val arr: [i64; 5] = [1, 2, 3, 4, 5]
    Then  expect arr[-1] == 5
    Then  expect arr[-2] == 4
    Then  expect arr[-3] == 3

### Scenario: Boundary Conditions

| # | Example | Status |
|---|---------|--------|
| 1 | handles single element arrays | pass |
| 2 | handles two element arrays | pass |

**Example:** handles single element arrays
    Given val single: [i64; 1] = [42]
    Then  expect single[0] == 42
    Then  expect single.len() == 1

**Example:** handles two element arrays
    Given val pair: [i64; 2] = [10, 20]
    Then  expect pair[0] == 10
    Then  expect pair[1] == 20
    Then  expect pair.len() == 2

### Scenario: Mixed Types

| # | Example | Status |
|---|---------|--------|
| 1 | works with string arrays | pass |
| 2 | works with boolean arrays | pass |

**Example:** works with string arrays
    Given val names: [text; 3] = ["alice", "bob", "charlie"]
    Then  expect names[0] == "alice"
    Then  expect names.len() == 3

**Example:** works with boolean arrays
    Given val flags: [bool; 2] = [true, false]
    Then  expect flags[0] == true
    Then  expect flags[1] == false

### Scenario: Functional Operations on Fixed

| # | Example | Status |
|---|---------|--------|
| 1 | map preserves values | pass |
| 2 | filter may reduce size | pass |
| 3 | reduce works on fixed arrays | pass |

**Example:** map preserves values
    Given val arr: [i64; 4] = [1, 2, 3, 4]
    Given val doubled = arr.map(\x: x * 2)
    Then  expect doubled.len() == 4
    Then  expect doubled[0] == 2
    Then  expect doubled[3] == 8

**Example:** filter may reduce size
    Given val arr: [i64; 5] = [1, 2, 3, 4, 5]
    Given val big = arr.filter(\x: x > 3)
    Then  expect big.len() == 2
    Then  expect big[0] == 4
    Then  expect big[1] == 5

**Example:** reduce works on fixed arrays
    Given val arr: [i64; 3] = [10, 20, 30]
    Given val total = arr.reduce(0, \acc, x: acc + x)
    Then  expect total == 60


