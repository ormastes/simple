# String Interpolation Specification
*Source:* `test/feature/usage/string_interpolation_spec.spl`
**Feature IDs:** #INTERP-001 to #INTERP-020  |  **Category:** Language | Syntax  |  **Status:** Implemented

## Overview


use std.text.{NL}

## Overview

String interpolation allows embedding expressions directly in string literals
using curly braces. Simple treats interpolation as the default for regular
strings, with raw strings available when needed.

## Syntax

```simple
# Default interpolation (no special prefix needed)
val name = "Alice"
print "Hello, {name}!"          # Output: Hello, Alice!

# Expressions in braces
print "Result: {2 + 3}"         # Output: Result: 5

# Raw strings (no interpolation)
val regex = r"pattern: \d+"     # Backslashes not escaped, no interpolation
```

## Key Concepts

| Concept | Syntax | Escaping | Interpolation |
|---------|--------|----------|---------------|
| Default String | `"..."` | Standard | Yes |
| Raw String | `r"..."` | None | No |
| Expression | `{expr}` | Within braces | Yes |
| Escape Sequence | `{NL}, \t, \\` | Standard | Processed |

## Behavior

- Expressions in braces are evaluated at runtime
- Any expression can appear in braces, not just variables
- Raw strings skip interpolation and escape processing

## Feature: Basic String Interpolation

## Basic String Interpolation

    Tests simple variable interpolation in strings.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | interpolates variable in string | pass |
| 2 | interpolates multiple variables | pass |
| 3 | interpolates at start of string | pass |
| 4 | interpolates at end of string | pass |

**Example:** interpolates variable in string
    Given val name = "Alice"
    Given val result = "Hello, {name}!"
    Given var r = 0
    Then  expect r == 1

**Example:** interpolates multiple variables
    Given val first = "John"
    Given val last = "Doe"
    Given val result = "{first} {last}"
    Given var r = 0
    Then  expect r == 1

**Example:** interpolates at start of string
    Given val value = 42
    Given val result = "{value} is the answer"
    Given var r = 0
    Then  expect r == 1

**Example:** interpolates at end of string
    Given val value = 42
    Given val result = "The answer is {value}"
    Given var r = 0
    Then  expect r == 1

## Feature: Expression Interpolation

## Expression Interpolation

    Tests that arbitrary expressions can be interpolated.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | interpolates arithmetic expression | pass |
| 2 | interpolates multiplication expression | pass |
| 3 | interpolates boolean value | pass |
| 4 | interpolates false boolean value | pass |

**Example:** interpolates arithmetic expression
    Given val a = 10
    Given val b = 20
    Given val result = "Sum: {a + b}"
    Given var r = 0
    Then  expect r == 1

**Example:** interpolates multiplication expression
    Given val x = 5
    Given val y = 3
    Given val result = "Product: {x * y}"
    Given var r = 0
    Then  expect r == 1

**Example:** interpolates boolean value
    Given val b = true
    Given val result = "flag: {b}"
    Given var r = 0
    Then  expect r == 1

**Example:** interpolates false boolean value
    Given val b = false
    Given val result = "flag: {b}"
    Given var r = 0
    Then  expect r == 1

## Feature: Raw Strings

## Raw Strings

    Tests raw strings with no interpolation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | raw string preserves braces | pass |
| 2 | raw string preserves backslashes | pass |

**Example:** raw string preserves braces
    Given val template = r"{name}"
    Then  expect template.len() == 6

**Example:** raw string preserves backslashes
    Given val path = r"C:\Users\test"
    Then  expect path.len() == 13

## Feature: F-String Syntax

## F-String Explicit Syntax

    Tests explicit f-string prefix (legacy compatibility).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | f-string basic interpolation | pass |
| 2 | f-string with expression | pass |
| 3 | f-string multiple interpolations | pass |
| 4 | f-string no interpolation | pass |

**Example:** f-string basic interpolation
    Given val x = 42
    Given val s = f"value is {x}"
    Given var r = 0
    Then  expect r == 1

**Example:** f-string with expression
    Given val a = 10
    Given val b = 20
    Given val s = f"sum is {a + b}"
    Given var r = 0
    Then  expect r == 1

**Example:** f-string multiple interpolations
    Given val name = "world"
    Given val count = 3
    Given val s = f"hello {name}, count={count}"
    Given var r = 0
    Then  expect r == 1

**Example:** f-string no interpolation
    Given val s = f"just a string"
    Given var r = 0
    Then  expect r == 1


