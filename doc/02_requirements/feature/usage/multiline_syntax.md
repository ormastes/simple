# Multi-line Syntax Specification
*Source:* `test/feature/usage/multiline_syntax_spec.spl`
**Feature IDs:** #MULTI-001  |  **Category:** Language | Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

## Overview

Tests for multi-line syntax patterns including function calls spanning
multiple lines, array literals, and continuation lines.

## Syntax

```simple
# Multi-line function call
val result = function_name(
    arg1,
    arg2,
    arg3
)

# Multi-line array
val items = [
    1,
    2,
    3
]

# Line continuation with backslash
val sum = 1 + 2 + \
    3 + 4
```

## Feature: Multi-line Function Calls

## Function Calls Spanning Multiple Lines

    Tests for calling functions with arguments on separate lines.

### Scenario: basic multi-line calls

| # | Example | Status |
|---|---------|--------|
| 1 | calls function with arguments on multiple lines | pass |
| 2 | calls function with named arguments on multiple lines | pass |

**Example:** calls function with arguments on multiple lines
    Given val result = add(
    Then  expect result == 3

**Example:** calls function with named arguments on multiple lines
    Given val result = greet(
    Then  expect result == 42

### Scenario: nested function calls

| # | Example | Status |
|---|---------|--------|
| 1 | nests function calls on single line | pass |
| 2 | nests function calls on multiple lines | pass |

**Example:** nests function calls on single line
    Then  expect outer(inner(5), inner(3)) == 16

**Example:** nests function calls on multiple lines
    Given val result = outer(
    Then  expect result == 16

## Feature: Multi-line Literals

## Array and Struct Literals Spanning Lines

    Tests for multi-line array and struct initialization.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates multi-line array literal | pass |
| 2 | creates multi-line struct initialization | pass |

**Example:** creates multi-line array literal
    Given val arr = [
    Then  expect arr[0] + arr[1] + arr[2] == 6

**Example:** creates multi-line struct initialization
    Given val c = Config_new(
    Then  expect c.value == 42

## Feature: Continuation Lines

## Line Continuation with Implicit Join

    Tests for implicit line continuation inside brackets/parens.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | continues function call to next line | pass |
| 2 | continues call at same indent level | pass |

**Example:** continues function call to next line
    Given val result = match_exception("ValueError", "some message",
    Then  expect result == 42

**Example:** continues call at same indent level
    Given val result = match_exception("ValueError", "some message",
    Then  expect result == 42

## Feature: Tuple Destructuring in Assignments

## Multi-line Tuple Patterns

    Tests for tuple destructuring assignments.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | destructures tuple from array element | pass |
| 2 | accesses tuple elements with dot notation | pass |
| 3 | destructures nested tuple data | pass |

**Example:** destructures tuple from array element
    Given val arr = [(10, 20)]
    Given val (a, b) = arr[0]
    Then  expect a + b == 30

**Example:** accesses tuple elements with dot notation
    Given val arr = [(10, 20)]
    Then  expect arr[0].0 + arr[0].1 == 30

**Example:** destructures nested tuple data
    Given val docstrings = [("content", 1), ("other", 2)]
    Given val (content, line) = docstrings[0]
    Then  expect line == 1


