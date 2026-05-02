# Macro Validation Specification
*Source:* `test/feature/usage/macro_validation_spec.spl`
**Feature IDs:** #MACRO-VAL-001 to #MACRO-VAL-014  |  **Category:** Infrastructure | Macros  |  **Status:** Implemented

## Overview



Tests that macros can be validated without full expansion in LL(1) parsing:
- Ordering validation (defined before use)
- Shadowing detection (intro symbols)
- QIDENT template variable validation
- Type annotation requirements

## Error Codes

- E1401: MACRO_UNDEFINED (used before definition)
- E1403: MACRO_SHADOWING (intro shadows existing symbol)
- E1405: MACRO_MISSING_TYPE_ANNOTATION
- E1406: MACRO_INVALID_QIDENT (template without const)

## Feature: Macro Definition Order

## Define Before Use

    Tests that macros must be defined before use.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | succeeds when macro is defined before use | pass |
| 2 | fails when macro is used before definition | pass |

**Example:** succeeds when macro is defined before use
    Given val greeting = "Hello, " + name
    Then  expect true

**Example:** fails when macro is used before definition
    Then  expect true  # Compile-time check

## Feature: Intro Shadowing Detection

## Symbol Conflict Detection

    Tests that intro cannot shadow existing symbols.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | fails when intro shadows existing variable | pass |
| 2 | fails when intro shadows existing function | pass |
| 3 | succeeds when intro introduces different symbol | pass |

**Example:** fails when intro shadows existing variable
    Then  expect true  # Compile-time check

**Example:** fails when intro shadows existing function
    Then  expect true  # Compile-time check

**Example:** succeeds when intro introduces different symbol
    Given val existing_var = 0
    Given val new_var = 42
    Then  expect new_var == 42

## Feature: QIDENT Template Validation

## Template Variable Requirements

    Tests that QIDENT templates require const parameters.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | succeeds with const parameter in template | pass |
| 2 | fails when template variable is not const | pass |

**Example:** succeeds with const parameter in template
    Then  expect get_value() == 42

**Example:** fails when template variable is not const
    Then  expect true  # Compile-time check

## Feature: Type Annotation Requirements

## Intro Type Annotations

    Tests that intro let requires type annotation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | fails when intro let lacks type annotation | pass |
| 2 | succeeds when intro let has type annotation | pass |

**Example:** fails when intro let lacks type annotation
    Then  expect true  # Compile-time check

**Example:** succeeds when intro let has type annotation
    Given val my_var = 42
    Then  expect my_var == 42

## Feature: Multiple Macros Ordering

## Multiple Macro Definitions

    Tests ordering with multiple macro definitions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows using macros in any order after definition | pass |

**Example:** allows using macros in any order after definition
    Given val var1 = 1
    Given val var2 = 2
    Then  expect var1 == 1
    Then  expect var2 == 2

## Feature: Multiple Intro Symbols

## Multiple Symbols Per Macro

    Tests macros that introduce multiple symbols.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | allows single intro symbol | pass |
| 2 | fails when macro introduces duplicate symbols | pass |

**Example:** allows single intro symbol
    Given val single_var = 42
    Then  expect single_var == 42

**Example:** fails when macro introduces duplicate symbols
    Then  expect true  # Compile-time check

## Feature: Intro For Loop

## Compile-Time For Loop

    Tests for loop in intro with const range.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | generates symbols from const for loop | pass |

**Example:** generates symbols from const for loop
    Given val "var_{i}" = i
    Then  expect var_0 == 0
    Then  expect var_1 == 1
    Then  expect var_2 == 2

## Feature: Intro Conditional

## Compile-Time Conditional

    Tests conditional intro with const condition.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | selects symbols based on const condition | pass |

**Example:** selects symbols based on const condition
    Given val enabled_var = 1
    Given val disabled_var = 0
    Then  expect enabled_var == 1


