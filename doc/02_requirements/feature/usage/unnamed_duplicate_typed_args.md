# Unnamed Duplicate Typed Arguments Warning Specification
*Source:* `test/feature/usage/unnamed_duplicate_typed_args_spec.spl`
**Feature IDs:** #LINT-001  |  **Category:** Lint  |  **Status:** Implemented

## Overview



use std.text.{NL}

This lint warns when a function has multiple parameters of the same type that
are passed positionally without named arguments. This helps prevent argument
order mistakes at call sites by encouraging explicit naming.

## Feature: Unnamed Duplicate Typed Args Warning

Verifies the `unnamed_duplicate_typed_args` lint that detects potential
    call site errors when functions have multiple parameters of the same type.
    The lint encourages using named arguments (e.g., `foo(a=x, b=y)`) instead
    of positional arguments (e.g., `foo(x, y)`) to prevent accidental argument
    swapping bugs. This is especially important for functions like `copy(from,
    to)` where swapping arguments silently produces wrong behavior.

### Scenario: functions with duplicate typed params

| # | Example | Status |
|---|---------|--------|
| 1 | warns on positional call with two text params | pass |
| 2 | accepts named arguments without warning | pass |
| 3 | works with mixed named and positional args | pass |

**Example:** warns on positional call with two text params
    Given val result = copy_text(src="source", dest="destination")
    Then  expect result == "destination"

**Example:** accepts named arguments without warning
    Given val (a, b) = swap(left=1, right=2)
    Then  expect a == 2
    Then  expect b == 1

**Example:** works with mixed named and positional args
    Given val ok = range_check(5, min=0, max=10)
    Then  expect ok == true

### Scenario: no warning cases

| # | Example | Status |
|---|---------|--------|
| 1 | does not warn on single parameter | pass |
| 2 | does not warn on different typed params | pass |
| 3 | does not warn when all params are named | pass |

**Example:** does not warn on single parameter
    Then  expect single("hello") == "hello"

**Example:** does not warn on different typed params
    Then  expect mixed("items", 5) == "items: 5"

**Example:** does not warn when all params are named
    Then  expect coords(x=1, y=2, z=3) == 6

### Scenario: real world examples

| # | Example | Status |
|---|---------|--------|
| 1 | copy function with named args | pass |
| 2 | compare function with named args | pass |
| 3 | move function with named args | pass |

**Example:** copy function with named args
    Given val msg = copy_file(source="/a/b.txt", dest="/c/d.txt")
    Then  expect msg == "Copied /a/b.txt to /c/d.txt"

**Example:** compare function with named args
    Then  expected == actual
    Then  expect compare(expected="hello", actual="hello") == true

**Example:** move function with named args
    Given val distance = move_item(from_pos=0, to_pos=10)
    Then  expect distance == 10


