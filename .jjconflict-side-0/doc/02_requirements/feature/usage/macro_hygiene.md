# Macro Hygiene Specification
*Source:* `test/feature/usage/macro_hygiene_spec.spl`
**Feature IDs:** #MACRO-001  |  **Category:** Language | Macros  |  **Status:** Implemented

## Overview



## Overview

Tests for macro hygiene system that prevents variable capture through
gensym renaming. Covers variable isolation, nested scopes, gensym uniqueness,
and pattern matching with hygiene.

## Syntax

```simple
macro make_ten() -> (returns result: Int):
    emit result:
        val x = 10
        x

val x = 5
val result = make_ten!()
# x is still 5, result is 10
```

## Feature: Basic Macro Hygiene

## Variable Capture Prevention

    Tests for basic macro variable isolation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | prevents variable capture | pass |
| 2 | isolates macro internal variables | pass |
| 3 | preserves outer variable after macro | pass |

**Example:** prevents variable capture
    Given val x = 10
    Given val x = 5
    Given val result = make_ten!()
    Then  expect x + result == 15

**Example:** isolates macro internal variables
    Given val temp = 1
    Given val a = increment!()
    Given val b = increment!()
    Then  expect a + b == 2

**Example:** preserves outer variable after macro
    Given val value = 100
    Given val value = 42
    Given val _ = do_nothing!()
    Then  expect value == 42

## Feature: Nested Scope Hygiene

## Nested Scopes in Macros

    Tests for hygiene with nested scopes.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles nested scopes in macro | pass |
| 2 | handles nested macro calls | pass |
| 3 | handles nested blocks | pass |

**Example:** handles nested scopes in macro
    Given val x = 10
    Given val inner = if true: 20 else: 0
    Then  expect nested_scopes!() == 30

**Example:** handles nested macro calls
    Given val x = 5
    Given val x = 10
    Then  expect outer!() == 15

**Example:** handles nested blocks
    Given val a = 1
    Given val b = if true: 2 + 3 else: 0
    Then  expect nested_blocks!() == 6

## Feature: Gensym Uniqueness

## Unique Variable Names per Invocation

    Tests for gensym'd variable uniqueness.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates unique names across calls | pass |
| 2 | gensyms multiple variables | pass |

**Example:** creates unique names across calls
    Given val count = 1
    Given val first = counter!()
    Given val second = counter!()
    Given val third = counter!()
    Then  expect first + second + third == 3

**Example:** gensyms multiple variables
    Given val a = 1
    Given val b = 2
    Given val c = 3
    Given val x = 10
    Given val y = 20
    Given val z = 30
    Given val result = multi_vars!()
    Then  expect x + y + z + result == 66

## Feature: Pattern Matching Hygiene

## Pattern Variables in Macros

    Tests for hygiene with pattern matching.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | isolates pattern variables | pass |
| 2 | isolates tuple destructuring | pass |
| 3 | isolates array destructuring | pass |

**Example:** isolates pattern variables
    Given val (x, y) = (10, 20)
    Given val x = 100
    Given val y = 200
    Given val result = make_pair!()
    Then  expect x + y + result == 330

**Example:** isolates tuple destructuring
    Given val (a, b) = (5, 10)
    Given val a = 1
    Given val b = 2
    Given val result = swap_values!()
    Then  expect a + b + result == 8

**Example:** isolates array destructuring
    Given val [x, y, z] = [1, 2, 3]
    Given val x = 10
    Given val y = 20
    Given val z = 30
    Given val result = sum_array!()
    Then  expect x + y + z + result == 66

## Feature: Function Parameter Hygiene

## Function Parameters in Macros

    Tests for hygiene with function definitions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | isolates function parameters | pass |
| 2 | isolates function from outer scope | pass |
| 3 | handles nested functions | pass |

**Example:** isolates function parameters
    Then  expect func_test!() == 10

**Example:** isolates function from outer scope
    Given val x = 100
    Given val result = func_macro!()
    Then  expect x + result == 110

**Example:** handles nested functions
    Then  expect nested_func!() == 15

## Feature: Complex Macro Hygiene

## Complex Scenarios

    Tests for complex hygiene scenarios.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles complex multi-scope macro | pass |
| 2 | handles macro parameters | pass |
| 3 | handles nested macros with same names | pass |

**Example:** handles complex multi-scope macro
    Given val temp = 1
    Given val sum1 = if true: 2 else: 0
    Given val sum2 = if true: 3 else: 0
    Given val sum3 = if true: 4 else: 0
    Then  expect complex!() == 10

**Example:** handles macro parameters
    Given val x = value + 10
    Given val x = 5
    Given val result = use_param!(32)
    Then  expect x + result == 47

**Example:** handles nested macros with same names
    Given val temp = n * 2
    Given val temp = 5
    Given val a = base!(temp)
    Given val b = base!(10)
    Then  expect wrapper!() == 35

## Feature: Macro Hygiene Edge Cases

## Edge Cases

    Tests for edge case scenarios.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles empty macro | pass |
| 2 | handles macro with early return | pass |
| 3 | handles variable shadowing | pass |

**Example:** handles empty macro
    Then  expect empty!() == 0

**Example:** handles macro with early return
    Given val x = 42
    Then  expect early_return!(false) == 42

**Example:** handles variable shadowing
    Given val x = 10
    Given val x = x + 5
    Given val x = x * 2
    Then  expect shadow_test!() == 30


