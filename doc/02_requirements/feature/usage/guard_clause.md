# Guard Clause Specification
*Source:* `test/feature/usage/guard_clause_spec.spl`
**Feature IDs:** #GUARD-CLAUSE  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

Guard clauses (pattern guards) allow conditional matching within pattern match arms.
They combine pattern matching with boolean conditions using the `if` keyword after
the pattern to provide additional filtering before the arm body executes.

## Syntax

```simple
match value:
    case pattern if condition:
        body
```

## Key Behaviors

- Guard conditions are evaluated after pattern matching succeeds
- Variables bound in the pattern are available in the guard condition
- If the guard evaluates to false, matching continues to the next arm
- Guards can reference external variables from the enclosing scope

## Feature: Guard Clauses

## Pattern Guard Specification

    Guard clauses provide conditional matching within match expressions.
    This test suite verifies:
    - Basic guard syntax with `case pattern if condition`
    - Variable binding access within guards
    - Guard evaluation order and fallthrough behavior
    - Interaction with different pattern types (literals, tuples, enums)
    - Complex guard expressions including comparisons and logical operators

### Scenario: basic integer guards

| # | Example | Status |
|---|---------|--------|
| 1 | matches when guard is true | pass |
| 2 | falls through when guard is false | pass |
| 3 | reaches default case when all guards fail | pass |

**Example:** matches when guard is true
    Then  expect classify(15) == "large"

**Example:** falls through when guard is false
    Then  expect classify(5) == "small"

**Example:** reaches default case when all guards fail
    Then  expect classify(-5) == "non-positive"

### Scenario: guards with equality checks

| # | Example | Status |
|---|---------|--------|
| 1 | matches exact value via guard | pass |

**Example:** matches exact value via guard
    Then  expect identify(0) == "zero"
    Then  expect identify(42) == "answer"
    Then  expect identify(99) == "other"

### Scenario: guards with tuple patterns

| # | Example | Status |
|---|---------|--------|
| 1 | uses bound variables in guard | pass |
| 2 | guards with multiple comparisons | pass |

**Example:** uses bound variables in guard
    Then  expect check_sum((60, 50)) == "big sum"
    Then  expect check_sum((5, 5)) == "equal"
    Then  expect check_sum((1, 2)) == "other"

**Example:** guards with multiple comparisons
    Then  expect check_range((5, 10)) == "both positive"
    Then  expect check_range((-5, -10)) == "both negative"
    Then  expect check_range((5, -10)) == "mixed"

### Scenario: guards with enum patterns

| # | Example | Status |
|---|---------|--------|
| 1 | filters enum payload with guard | pass |

**Example:** filters enum payload with guard
    Then  expect categorize(Value::Num(200)) == "large number"
    Then  expect categorize(Value::Num(50)) == "small number"
    Then  expect categorize(Value::Num(-5)) == "non-positive"
    Then  expect categorize(Value::Empty) == "empty"

### Scenario: guards with external variables

| # | Example | Status |
|---|---------|--------|
| 1 | references variables from outer scope | pass |

**Example:** references variables from outer scope
    Given val threshold = 50
    Then  expect above_threshold(75) == true
    Then  expect above_threshold(25) == false

### Scenario: guards with complex expressions

| # | Example | Status |
|---|---------|--------|
| 1 | uses modulo in guard | pass |
| 2 | uses logical or in guard | pass |

**Example:** uses modulo in guard
    Then  expect parity(10) == "even"
    Then  expect parity(7) == "odd"

**Example:** uses logical or in guard
    Then  expect is_special(1) == true
    Then  expect is_special(42) == true
    Then  expect is_special(100) == true
    Then  expect is_special(50) == false


