# Elif Val/Var Pattern Binding Specification
*Source:* `test/feature/usage/elif_val_pattern_binding_spec.spl`
**Feature IDs:** #1001  |  **Category:** Language  |  **Status:** Implemented

## Overview



use std.text.{NL}

## Overview

Tests for `elif val`/`elif var` pattern binding in conditional branches.
Verifies that pattern matching works correctly in elif positions,
matching the existing `if val` support.

## Syntax

```simple
if val Some(x) = expr1:
    use(x)
elif val Some(y) = expr2:
    use(y)
elif condition:
    fallback()
else:
    default()
```

## Feature: Elif Val Pattern Binding

Tests for elif val/var pattern matching in conditional branches.

### Scenario: basic elif val matching

### Scenario: Basic pattern binding in elif

        Tests that elif val correctly matches patterns and binds variables.

| # | Example | Status |
|---|---------|--------|
| 1 | matches elif val when if condition is false | pass |
| 2 | skips elif val when pattern does not match | pass |
| 3 | binds variable from elif val pattern | pass |

**Example:** matches elif val when if condition is false
    Given val x = Some(42)
    Given var result = ""
    Then  expect result == "elif=42"

**Example:** skips elif val when pattern does not match
    Given var result = "default"
    Then  expect result == "default"

**Example:** binds variable from elif val pattern
    Given val data = Some("hello")
    Given var captured = ""
    Then  expect captured == "hello"

### Scenario: elif val with else fallback

### Scenario: Pattern binding with else

        Tests elif val falling through to else when no pattern matches.

| # | Example | Status |
|---|---------|--------|
| 1 | falls to else when elif val does not match | pass |
| 2 | does not reach else when elif val matches | pass |

**Example:** falls to else when elif val does not match
    Given var result = ""
    Then  expect result == "else"

**Example:** does not reach else when elif val matches
    Given var result = ""
    Then  expect result == "elif=99"

### Scenario: multiple elif val branches

### Scenario: Chained pattern bindings

        Tests multiple elif val branches evaluated in order.

| # | Example | Status |
|---|---------|--------|
| 1 | matches first elif val pattern | pass |
| 2 | matches second elif val when first does not match | pass |
| 3 | falls through all elif val when none match | pass |

**Example:** matches first elif val pattern
    Given val a = Some(1)
    Given val b = Some(2)
    Given var result = ""
    Then  expect result == "first=1"

**Example:** matches second elif val when first does not match
    Given val b = Some(2)
    Given var result = ""
    Then  expect result == "second=2"

**Example:** falls through all elif val when none match
    Given var result = "none"
    Then  expect result == "none"

### Scenario: mixed elif and elif val

### Scenario: Regular elif mixed with pattern elif

        Tests combining regular boolean elif with elif val pattern binding.

| # | Example | Status |
|---|---------|--------|
| 1 | matches regular elif before elif val | pass |
| 2 | matches elif val after failed regular elif | pass |
| 3 | matches regular elif after failed elif val | pass |
| 4 | reaches else after mixed elif failures | pass |

**Example:** matches regular elif before elif val
    Given var result = ""
    Then  expect result == "elif-bool"

**Example:** matches elif val after failed regular elif
    Given val x = Some(10)
    Given var result = ""
    Then  expect result == "elif-val=10"

**Example:** matches regular elif after failed elif val
    Given var result = ""
    Then  expect result == "elif-bool"

**Example:** reaches else after mixed elif failures
    Given var result = ""
    Then  expect result == "else"

### Scenario: if val combined with elif val

### Scenario: Pattern binding in both if and elif

        Tests if val at the top combined with elif val.

| # | Example | Status |
|---|---------|--------|
| 1 | matches if val and skips elif val | pass |
| 2 | skips if val and matches elif val | pass |
| 3 | skips both if val and elif val to else | pass |

**Example:** matches if val and skips elif val
    Given var result = ""
    Then  expect result == "if=1"

**Example:** skips if val and matches elif val
    Given var result = ""
    Then  expect result == "elif=2"

**Example:** skips both if val and elif val to else
    Given var result = ""
    Then  expect result == "else"

### Scenario: nested option patterns

### Scenario: Various Option patterns in elif val

        Tests nested and varied Option patterns in elif val.

| # | Example | Status |
|---|---------|--------|
| 1 | matches nested Some in elif val | pass |
| 2 | chains multiple Some patterns | pass |

**Example:** matches nested Some in elif val
    Given val inner = Some(Some(99))
    Given var result = ""
    Then  expect result == "nested=99"

**Example:** chains multiple Some patterns
    Given val a = None
    Given val b = None
    Given val c = Some(7)
    Given var result = ""
    Then  expect result == "c=7"

### Scenario: elif val as implicit return

### Scenario: Elif val in expression position

        Tests elif val when the if-elif-else is the last expression in a function.

| # | Example | Status |
|---|---------|--------|
| 1 | returns from elif val branch | pass |

**Example:** returns from elif val branch
    Then  expect classify(Some(7)) == "got=7"
    Then  expect classify(None) == "nothing"

### Scenario: elif val scope isolation

### Scenario: Variable scope in elif val bindings

        Tests that bindings from elif val are properly scoped.

| # | Example | Status |
|---|---------|--------|
| 1 | bindings do not leak to outer scope | pass |

**Example:** bindings do not leak to outer scope
    Given var outer = "unchanged"
    Then  expect outer == "n=42"

### Scenario: elif val with nil/no-match returns nil

### Scenario: No branch matches returns nil

        Tests that when no if/elif/else matches, the result is nil.

| # | Example | Status |
|---|---------|--------|
| 1 | returns nil when no branch matches | pass |

**Example:** returns nil when no branch matches
    Given var result = "before"
    Then  expect result == "before"


