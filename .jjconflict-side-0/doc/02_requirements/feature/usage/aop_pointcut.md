# AOP Pointcut Expression Specification
*Source:* `test/feature/usage/aop_pointcut_spec.spl`
**Feature IDs:** #AOP-PC-001 to #AOP-PC-015  |  **Category:** Language  |  **Status:** In Progress

## Overview


**Tags:** aop

Pointcut expressions define where advice should be applied. The `pc{...}` syntactic
island contains pointcut predicates that match against the program structure.

## Syntax

```simple
pc{ selector(pattern) }
pc{ selector1(...) & selector2(...) }  # AND
pc{ selector1(...) | selector2(...) }  # OR
pc{ !selector(...) }                   # NOT
```

## Selectors

| Selector | Description | Example |
|----------|-------------|---------|
| execution | Match function execution | `execution(* foo(..))` |
| within | Match code in module/class | `within(services.*)` |
| attr | Match by attribute | `attr(logged)` |

## Limitations (Current Implementation)

- Init selector not yet implemented (requires around advice)
- Inline module definitions in test blocks not supported

## Feature: Execution Pointcut Selector

## execution(signature) Selector

    Matches join points at function execution. The signature pattern includes
    return type, function name, and parameter types.

### Scenario: return type patterns

| # | Example | Status |
|---|---------|--------|
| 1 | matches any return type with wildcard | pass |

**Example:** matches any return type with wildcard
    Given var matched = false
    Then  expect matched == true
    Then  expect matched == true

### Scenario: function name patterns

| # | Example | Status |
|---|---------|--------|
| 1 | matches exact function name | pass |
| 2 | matches prefix wildcard | pass |
| 3 | matches suffix wildcard | pass |

**Example:** matches exact function name
    Given var called = false
    Then  expect called == true

**Example:** matches prefix wildcard
    Given var count = 0
    Then  expect count == 2

**Example:** matches suffix wildcard
    Given var count = 0
    Then  expect count == 2

### Scenario: parameter patterns

| # | Example | Status |
|---|---------|--------|
| 1 | matches any parameters with (..) | pass |

**Example:** matches any parameters with (..)
    Given var called = false
    Then  expect called == true
    Then  expect called == true
    Then  expect called == true

## Feature: Attribute Pointcut Selector

## attr(name) Selector

    Matches join points on elements decorated with the specified attribute.

### Scenario: function attributes

| # | Example | Status |
|---|---------|--------|
| 1 | matches function with attribute | pass |
| 2 | matches multiple attributes | pass |

**Example:** matches function with attribute
    Given var logged = false
    Then  expect logged == true
    Then  expect logged == false

**Example:** matches multiple attributes
    Given var count = 0
    Then  expect count == 1
    Then  expect count == 1  # Still 1, regular doesn't have @critical

## Feature: Pointcut Logical Operators

## Combining Pointcuts

    Pointcuts can be combined using logical operators with precedence:
    ! (NOT) > & (AND) > | (OR)

### Scenario: AND operator

| # | Example | Status |
|---|---------|--------|
| 1 | requires both conditions | pass |

**Example:** requires both conditions
    Given var called = false
    Then  expect called == true
    Then  expect called == false  # Missing @important
    Then  expect called == false  # Not *_calc

### Scenario: OR operator

| # | Example | Status |
|---|---------|--------|
| 1 | matches either condition | pass |

**Example:** matches either condition
    Given var count = 0
    Then  expect count == 2

### Scenario: NOT operator

| # | Example | Status |
|---|---------|--------|
| 1 | excludes matching pointcuts | pass |

**Example:** excludes matching pointcuts
    Given var count = 0
    Then  expect count == 1

## Feature: Wildcard Patterns in Pointcuts

## Path and Name Wildcards

    Wildcards allow flexible matching in pointcut expressions:
    - `*` matches one segment/character sequence

### Scenario: prefix and suffix wildcards

| # | Example | Status |
|---|---------|--------|
| 1 | matches prefix with name* | pass |
| 2 | matches suffix with *name | pass |

**Example:** matches prefix with name*
    Given var count = 0
    Then  expect count == 2

**Example:** matches suffix with *name
    Given var count = 0
    Then  expect count == 2


