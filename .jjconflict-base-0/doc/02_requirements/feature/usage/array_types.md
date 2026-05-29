# array types
*Source:* `test/feature/usage/array_types_spec.spl`

## Overview

Array Types Tests
Feature: Array type system and operations
Category: Type System Features
Status: Implemented

Tests for array type declarations, indexing, operations, and functional methods.

## Feature: Array Basics

## Array Literal and Indexing

    Tests for array creation, indexing, and basic operations.

### Scenario: array literals

| # | Example | Status |
|---|---------|--------|
| 1 | creates array from literal | pass |
| 2 | gets array length | pass |
| 3 | gets first and last elements | pass |

**Example:** creates array from literal
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[2] == 3

**Example:** gets array length
    Given val arr = [10, 20, 30]
    Then  expect arr.len() == 3

**Example:** gets first and last elements
    Given val arr = [5, 10, 15, 20]
    Then  expect arr.first() + arr.last() == 25

### Scenario: array queries

| # | Example | Status |
|---|---------|--------|
| 1 | checks if array contains element | pass |
| 2 | checks if array is empty | pass |
| 3 | checks non-empty array | pass |

**Example:** checks if array contains element
    Given val arr = [1, 2, 3]
    Then  expect arr.contains(2)

**Example:** checks if array is empty
    Given val arr = []
    Then  expect arr.is_empty()

**Example:** checks non-empty array
    Given val arr = [1]
    Then  expect not arr.is_empty()

## Feature: Array Modification

## Array Mutation Operations

    Tests for push, concat, and other modifying operations.

### Scenario: push and concat

| # | Example | Status |
|---|---------|--------|
| 1 | pushes element to array | pass |
| 2 | concatenates two arrays | pass |

**Example:** pushes element to array
    Given var arr = [1, 2, 3]
    Then  expect arr[3] == 4

**Example:** concatenates two arrays
    Given val a = [1, 2]
    Given val b = [3, 4]
    Given val c = a.concat(b)
    Then  expect c.len() == 4

### Scenario: reverse

| # | Example | Status |
|---|---------|--------|
| 1 | reverses array | pass |

**Example:** reverses array
    Given val arr = [1, 2, 3]
    Given val rev = arr.reverse()
    Then  expect rev[0] == 3

## Feature: Array Functional Methods

## Functional Programming on Arrays

    Tests for map, filter, reduce, and other functional operations.

### Scenario: map

| # | Example | Status |
|---|---------|--------|
| 1 | maps function over array | pass |

**Example:** maps function over array
    Given val arr = [1, 2, 3]
    Given val doubled = arr.map(\x: x * 2)
    Then  expect doubled[1] == 4

### Scenario: filter

| # | Example | Status |
|---|---------|--------|
| 1 | filters array by predicate | pass |

**Example:** filters array by predicate
    Given val arr = [1, 2, 3, 4, 5]
    Given val evens = arr.filter(\x: x % 2 == 0)
    Then  expect evens.len() == 2

### Scenario: reduce

| # | Example | Status |
|---|---------|--------|
| 1 | reduces array with accumulator | pass |

**Example:** reduces array with accumulator
    Given val arr = [1, 2, 3, 4, 5]
    Given val sum = arr.reduce(0, \acc, x: acc + x)
    Then  expect sum == 15

### Scenario: all and any

| # | Example | Status |
|---|---------|--------|
| 1 | checks all elements match predicate | pass |

**Example:** checks all elements match predicate
    Given val arr = [2, 4, 6]
    Given val all_even = arr.all(\x: x % 2 == 0)
    Then  expect all_even

### Scenario: join

| # | Example | Status |
|---|---------|--------|
| 1 | joins array elements with separator | pass |

**Example:** joins array elements with separator
    Given val arr = [1, 2, 3]
    Given val s = arr.join("-")
    Then  expect s == "1-2-3"

### Scenario: sum

| # | Example | Status |
|---|---------|--------|
| 1 | sums numeric array | pass |

**Example:** sums numeric array
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr.sum() == 15

## Feature: Array Slicing

## Python-Style Slice Syntax

    Tests for array slicing with start:end:step notation.

### Scenario: basic slicing

| # | Example | Status |
|---|---------|--------|
| 1 | slices with start and end | pass |
| 2 | slices from start index to end | pass |
| 3 | slices from beginning to end index | pass |

**Example:** slices with start and end
    Given val arr = [0, 1, 2, 3, 4, 5]
    Given val sub = arr[1:4]
    Then  expect sub.len() == 3

**Example:** slices from start index to end
    Given val arr = [0, 1, 2, 3, 4]
    Given val sub = arr[2:]
    Then  expect sub[0] == 2

**Example:** slices from beginning to end index
    Given val arr = [0, 1, 2, 3, 4]
    Given val sub = arr[:3]
    Then  expect sub.len() == 3

### Scenario: step slicing

| # | Example | Status |
|---|---------|--------|
| 1 | slices with step | pass |

**Example:** slices with step
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7]
    Given val evens = arr[::2]
    Then  expect evens.len() == 4

## Feature: Negative Indexing

## Python-Style Negative Indices

    Tests for accessing elements from end of array.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | gets last element with -1 | pass |
| 2 | gets second from end with -2 | pass |

**Example:** gets last element with -1
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[-1] == 50

**Example:** gets second from end with -2
    Given val arr = [1, 2, 3, 4, 5]
    Then  expect arr[-2] == 4

## Feature: Array Spread Operator

## Spread Syntax for Arrays

    Tests for spreading arrays into other arrays.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | spreads arrays with * | pass |
| 2 | spreads array mixed with elements | pass |

**Example:** spreads arrays with *
    Given val a = [1, 2, 3]
    Given val b = [4, 5]
    Given val c = [*a, *b]
    Then  expect c.len() == 5

**Example:** spreads array mixed with elements
    Given val a = [2, 3]
    Given val arr = [1, *a, 4]
    Then  expect arr[2] == 3

## Feature: List Comprehension

## Comprehension Syntax

    Tests for creating arrays with comprehension expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates list from comprehension | pass |
| 2 | filters with comprehension condition | pass |
| 3 | creates squares with comprehension | pass |

**Example:** creates list from comprehension
    Given val arr = [1, 2, 3, 4, 5]
    Given val doubled = [x * 2 for x in arr]
    Then  expect doubled[2] == 6

**Example:** filters with comprehension condition
    Given val arr = [1, 2, 3, 4, 5, 6]
    Given val evens = [x for x in arr if x % 2 == 0]
    Then  expect evens.len() == 3

**Example:** creates squares with comprehension
    Given val squares = [x * x for x in [1, 2, 3, 4]]
    Then  expect squares[3] == 16

## Feature: Chained Comparisons

## Python-Style Chained Comparisons

    Tests for a < b < c style comparisons.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates basic chained comparison | pass |
| 2 | evaluates false chained comparison | pass |
| 3 | evaluates three-way comparison | pass |
| 4 | evaluates mixed comparison operators | pass |

**Example:** evaluates basic chained comparison
    Given val x = 5
    Then  expect 0 < x and x < 10

**Example:** evaluates false chained comparison
    Given val x = 15
    Then  expect not (0 < x and x < 10)

**Example:** evaluates three-way comparison
    Given val a = 1
    Given val b = 5
    Given val c = 10
    Then  expect a < b and b < c

**Example:** evaluates mixed comparison operators
    Given val x = 5
    Then  expect 0 <= x and x <= 10


