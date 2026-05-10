# placeholder lambda
*Source:* `test/feature/usage/placeholder_lambda_spec.spl`

## Overview

Placeholder Lambda Specification

Category: Syntax
Status: Implemented

Placeholder lambdas transform `_` in expressions into anonymous function parameters.
- `_ * 2` becomes `\__p0: __p0 * 2`
- `_ + _` becomes `\__p0, __p1: __p0 + __p1`
- `_.field` becomes `\__p0: __p0.field`

## Feature: Placeholder Lambda

### Scenario: filter with comparison

| # | Example | Status |
|---|---------|--------|
| 1 | filters with less than | pass |
| 2 | filters with greater than | pass |
| 3 | filters with less than or equal | pass |
| 4 | filters with greater than or equal | pass |
| 5 | filters with equality | pass |
| 6 | filters with not equal | pass |

**Example:** filters with less than
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data.filter(_ < 3)
    Then  expect result == [1, 2]

**Example:** filters with greater than
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data.filter(_ > 3)
    Then  expect result == [4, 5]

**Example:** filters with less than or equal
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data.filter(_ <= 3)
    Then  expect result == [1, 2, 3]

**Example:** filters with greater than or equal
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data.filter(_ >= 3)
    Then  expect result == [3, 4, 5]

**Example:** filters with equality
    Given val data = [1, 2, 3, 2, 1]
    Given val result = data.filter(_ == 2)
    Then  expect result == [2, 2]

**Example:** filters with not equal
    Given val data = [1, 2, 3, 2, 1]
    Given val result = data.filter(_ != 2)
    Then  expect result == [1, 3, 1]

### Scenario: map with arithmetic

| # | Example | Status |
|---|---------|--------|
| 1 | maps with multiply | pass |
| 2 | maps with add | pass |
| 3 | maps with subtract | pass |
| 4 | maps with negate | pass |

**Example:** maps with multiply
    Given val data = [1, 2, 3]
    Given val result = data.map(_ * 10)
    Then  expect result == [10, 20, 30]

**Example:** maps with add
    Given val data = [1, 2, 3]
    Given val result = data.map(_ + 100)
    Then  expect result == [101, 102, 103]

**Example:** maps with subtract
    Given val data = [10, 20, 30]
    Given val result = data.map(_ - 5)
    Then  expect result == [5, 15, 25]

**Example:** maps with negate
    Given val data = [1, 2, 3]
    Given val result = data.map(-_)
    Then  expect result == [-1, -2, -3]

### Scenario: chaining

| # | Example | Status |
|---|---------|--------|
| 1 | chains filter then map | pass |
| 2 | chains map then filter | pass |

**Example:** chains filter then map
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data.filter(_ > 2).map(_ * 2)
    Then  expect result == [6, 8, 10]

**Example:** chains map then filter
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data.map(_ * 2).filter(_ > 5)
    Then  expect result == [6, 8, 10]

### Scenario: string operations

| # | Example | Status |
|---|---------|--------|
| 1 | filters strings by length | pass |

**Example:** filters strings by length
    Given val words = ["hi", "hello", "hey", "howdy"]
    Given val result = words.filter(_.len() > 3)
    Then  expect result == ["hello", "howdy"]

### Scenario: complex expressions

| # | Example | Status |
|---|---------|--------|
| 1 | uses placeholder in modulo | pass |
| 2 | uses placeholder in compound expression | pass |

**Example:** uses placeholder in modulo
    Given val data = [1, 2, 3, 4, 5, 6]
    Given val result = data.filter(_ % 2 == 0)
    Then  expect result == [2, 4, 6]

**Example:** uses placeholder in compound expression
    Given val data = [1, 2, 3, 4, 5]
    Given val result = data.map(_ * 2 + 1)
    Then  expect result == [3, 5, 7, 9, 11]

### Scenario: with different collection methods

| # | Example | Status |
|---|---------|--------|
| 1 | works with any | pass |
| 2 | works with all | pass |
| 3 | works with all returning false | pass |

**Example:** works with any
    Given val data = [1, 2, 3]
    Given val result = data.any(_ > 2)
    Then  expect result == true

**Example:** works with all
    Given val data = [2, 4, 6]
    Given val result = data.all(_ % 2 == 0)
    Then  expect result == true

**Example:** works with all returning false
    Given val data = [2, 3, 6]
    Given val result = data.all(_ % 2 == 0)
    Then  expect result == false

### Scenario: empty collections

| # | Example | Status |
|---|---------|--------|
| 1 | filter on empty returns empty | pass |
| 2 | map on empty returns empty | pass |

**Example:** filter on empty returns empty
    Given val data: [i64] = []
    Given val result = data.filter(_ > 0)
    Then  expect result == []

**Example:** map on empty returns empty
    Given val data: [i64] = []
    Given val result = data.map(_ * 2)
    Then  expect result == []

### Scenario: single element

| # | Example | Status |
|---|---------|--------|
| 1 | filter matching single element | pass |
| 2 | filter non-matching single element | pass |

**Example:** filter matching single element
    Given val data = [42]
    Given val result = data.filter(_ == 42)
    Then  expect result == [42]

**Example:** filter non-matching single element
    Given val data = [42]
    Given val result = data.filter(_ == 0)
    Then  expect result == []


