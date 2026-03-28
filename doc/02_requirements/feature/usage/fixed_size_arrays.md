# fixed size arrays
*Source:* `test/feature/usage/fixed_size_arrays_spec.spl`

## Overview

Fixed-Size Arrays - Comprehensive SSpec Tests
Decision #8: [T; N] syntax with runtime size checking

Category: Collections
Status: Implemented (Part 2/2)

## Feature: Fixed-Size Arrays

### Scenario: Basic Syntax

| # | Example | Status |
|---|---------|--------|
| 1 | creates fixed-size array with type annotation | pass |
| 2 | creates fixed-size int array | pass |
| 3 | creates single element fixed-size array | pass |

**Example:** creates fixed-size array with type annotation
    Given val vec3: [f64; 3] = [1.0, 2.0, 3.0]
    Then  expect vec3.len() == 3

**Example:** creates fixed-size int array
    Given val arr: [i64; 5] = [1, 2, 3, 4, 5]
    Then  expect arr.len() == 5

**Example:** creates single element fixed-size array
    Given val arr: [i64; 1] = [42]
    Then  expect arr.len() == 1
    Then  expect arr[0] == 42

### Scenario: Indexing

| # | Example | Status |
|---|---------|--------|
| 1 | allows indexing read | pass |
| 2 | allows negative indexing | pass |

**Example:** allows indexing read
    Given val vec3: [f64; 3] = [1.0, 2.0, 3.0]
    Then  expect vec3[0] == 1.0
    Then  expect vec3[1] == 2.0
    Then  expect vec3[2] == 3.0

**Example:** allows negative indexing
    Given val arr: [i64; 3] = [10, 20, 30]
    Then  expect arr[-1] == 30
    Then  expect arr[-2] == 20
    Then  expect arr[-3] == 10

### Scenario: Read Operations

| # | Example | Status |
|---|---------|--------|
| 1 | allows len | pass |
| 2 | allows first and last | pass |
| 3 | allows contains | pass |
| 4 | allows iteration | pass |

**Example:** allows len
    Given val vec3: [f64; 3] = [1.0, 2.0, 3.0]
    Then  expect vec3.len() == 3

**Example:** allows first and last
    Given val arr: [i64; 4] = [10, 20, 30, 40]
    Then  expect arr.first() == 10
    Then  expect arr.last() == 40

**Example:** allows contains
    Given val arr: [i64; 3] = [1, 2, 3]
    Then  expect arr.contains(2)
    Then  expect not arr.contains(5)

**Example:** allows iteration
    Given val vec3: [i64; 3] = [1, 2, 3]
    Given var sum = 0
    Then  expect sum == 6

### Scenario: Functional Operations

| # | Example | Status |
|---|---------|--------|
| 1 | allows map (returns dynamic array) | pass |
| 2 | allows filter (returns dynamic array) | pass |
| 3 | allows reduce | pass |

**Example:** allows map (returns dynamic array)
    Given val vec3: [i64; 3] = [1, 2, 3]
    Given val doubled = vec3.map(\x: x * 2)
    Then  expect doubled[0] == 2
    Then  expect doubled[1] == 4
    Then  expect doubled[2] == 6

**Example:** allows filter (returns dynamic array)
    Given val arr: [i64; 5] = [1, 2, 3, 4, 5]
    Given val evens = arr.filter(\x: x % 2 == 0)
    Then  expect evens.len() == 2
    Then  expect evens[0] == 2

**Example:** allows reduce
    Given val arr: [i64; 4] = [1, 2, 3, 4]
    Given val sum = arr.reduce(0, \acc, x: acc + x)
    Then  expect sum == 10

### Scenario: Display Format

| # | Example | Status |
|---|---------|--------|
| 1 | displays with size annotation | pass |

**Example:** displays with size annotation
    Given val vec3: [i64; 3] = [1, 2, 3]
    Then  expect vec3.len() == 3


