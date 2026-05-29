# Advanced Indexing and Slicing Specification
*Source:* `test/feature/usage/advanced_indexing_spec.spl`
**Feature IDs:** #1015, #1016, #1017  |  **Category:** Language, Collections  |  **Status:** Complete

## Overview



use std.text.{NL}

Tests for advanced indexing features including:
- Negative indexing (Python-style -1, -2, etc.)
- Slice operations with start:end:step syntax
- String slicing
- Multi-dimensional indexing

## Feature: Advanced Indexing

Tests for negative indexing and advanced array/string access patterns.

### Scenario: negative indexing

### Scenario: Negative Indexing

        Python-style negative indexing where -1 is the last element,
        -2 is second-to-last, etc.

| # | Example | Status |
|---|---------|--------|
| 1 | accesses last element with -1 | pass |
| 2 | accesses second-to-last with -2 | pass |
| 3 | accesses first element with negative index | pass |
| 4 | works with strings | pass |
| 5 | negative indexing with single element | pass |

**Example:** accesses last element with -1
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[-1] == 50

**Example:** accesses second-to-last with -2
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[-2] == 40

**Example:** accesses first element with negative index
    Given val arr = [10, 20, 30]
    Then  expect arr[-3] == 10

**Example:** works with strings
    Given val s = "Hello"
    Then  expect s[-1] == "o"
    Then  expect s[-5] == "H"

**Example:** negative indexing with single element
    Given val arr = [42]
    Then  expect arr[-1] == 42

### Scenario: slicing operations

### Scenario: Array Slicing

        Tests slice syntax arr[start:end:step] with various combinations.

| # | Example | Status |
|---|---------|--------|
| 1 | slices with start and end | pass |
| 2 | slices from beginning | pass |
| 3 | slices to end | pass |
| 4 | slices with step | pass |
| 5 | reverses with negative step | pass |
| 6 | slices with start:end:step | pass |
| 7 | empty slice | pass |

**Example:** slices with start and end
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[1:4] == [20, 30, 40]

**Example:** slices from beginning
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[:3] == [10, 20, 30]

**Example:** slices to end
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[2:] == [30, 40, 50]

**Example:** slices with step
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[::2] == [10, 30, 50]

**Example:** reverses with negative step
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[::-1] == [50, 40, 30, 20, 10]

**Example:** slices with start:end:step
    Given val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    Then  expect arr[2:8:2] == [2, 4, 6]

**Example:** empty slice
    Given val arr = [10, 20, 30]
    Then  expect arr[5:10] == []

### Scenario: string slicing

### Scenario: String Slicing

        Slicing operations on strings (UTF-8 aware).

| # | Example | Status |
|---|---------|--------|
| 1 | slices substring | pass |
| 2 | slices from end | pass |
| 3 | slices middle | pass |
| 4 | reverses string | pass |
| 5 | handles UTF-8 characters | pass |

**Example:** slices substring
    Given val s = "Hello World"
    Then  expect s[0:5] == "Hello"

**Example:** slices from end
    Given val s = "Hello World"
    Then  expect s[-5:] == "World"

**Example:** slices middle
    Given val s = "abcdefgh"
    Then  expect s[2:6] == "cdef"

**Example:** reverses string
    Given val s = "Hello"
    Then  expect s[::-1] == "olleH"

**Example:** handles UTF-8 characters
    Given val s = "Hello 🌍 World"
    Then  expect s[6:7] == "🌍"

### Scenario: combined operations

### Scenario: Combining Negative Index and Slicing

        Using negative indices in slice expressions.

| # | Example | Status |
|---|---------|--------|
| 1 | slices with negative start | pass |
| 2 | slices with negative end | pass |
| 3 | slices with both negative | pass |
| 4 | negative indices in string slice | pass |

**Example:** slices with negative start
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[-3:] == [30, 40, 50]

**Example:** slices with negative end
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[:-2] == [10, 20, 30]

**Example:** slices with both negative
    Given val arr = [10, 20, 30, 40, 50]
    Then  expect arr[-4:-1] == [20, 30, 40]

**Example:** negative indices in string slice
    Given val s = "Hello World"
    Then  expect s[-5:-1] == "Worl"


