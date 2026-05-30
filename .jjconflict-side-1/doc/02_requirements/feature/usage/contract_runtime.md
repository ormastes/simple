# Contract Runtime Specification
*Source:* `test/feature/usage/contract_runtime_spec.spl`
**Feature IDs:** #CONTRACT-RT-001 to #CONTRACT-RT-031  |  **Category:** Type System | Contracts  |  **Status:** Implemented

## Overview



Tests that contract checks execute correctly at runtime, including
preconditions, postconditions, invariants, and old() capture.

## Contract Syntax

```simple
fn transfer(from: i64, to: i64, amount: i64) -> (i64, i64):
    in:
        amount > 0
        from >= amount
    invariant:
        from >= 0
        to >= 0
    out(res):
        res.0 == old(from) - amount
        res.1 == old(to) + amount
    # function body
```

## Feature: Basic old() Capture

## Pre-State Capture

    Tests that old() correctly captures values before function execution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | captures simple parameter value | pass |
| 2 | captures multiple parameters | pass |
| 3 | captures field access | pass |
| 4 | captures complex expression | pass |

**Example:** captures simple parameter value
    Then  expect increment(41) == 42

**Example:** captures multiple parameters
    Then  expect swap_and_sum(20, 22) == 42

**Example:** captures field access
    Given var c = Counter(value: 41)
    Then  expect c.value == 42

**Example:** captures complex expression
    Given val doubled = x * 2
    Then  expect double_and_square(3) == 36

## Feature: Precondition Lowering

## Input Validation

    Tests that preconditions are checked before function execution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates basic precondition | pass |
| 2 | validates multiple preconditions | pass |

**Example:** validates basic precondition
    Then  expect divide(84, 2) == 42

**Example:** validates multiple preconditions
    Then  expect bounded_divide(84, 2, 100) == 42

## Feature: Postcondition Lowering

## Output Validation

    Tests that postconditions are checked after function execution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates basic postcondition | pass |
| 2 | validates multiple postconditions | pass |

**Example:** validates basic postcondition
    Then  expect abs_value(-42) == 42

**Example:** validates multiple postconditions
    Then  expect compute_positive(32) == 42

## Feature: Invariant Lowering

## Invariant Checking

    Tests that invariants hold throughout function execution.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates basic invariant | pass |

**Example:** validates basic invariant
    Then  expect process(41) == 42

## Feature: Combined Contracts with old()

## Full Contract Specification

    Tests functions with precondition, postcondition, and invariant.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates transfer function | pass |
| 2 | validates custom binding in postcondition | pass |

**Example:** validates transfer function
    Given val new_from = from_balance - amount
    Given val new_to = to_balance + amount
    Given val (from, to) = transfer(100, 50, 30)
    Then  expect from == 70
    Then  expect to == 80

**Example:** validates custom binding in postcondition
    Then  expect compute(32) == 42

## Feature: Multiple old() References

## Repeated old() Usage

    Tests multiple references to same old() expression.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles multiple references to same old() | pass |
| 2 | handles old() with different params | pass |

**Example:** handles multiple references to same old()
    Then  expect double_check(21) == 42

**Example:** handles old() with different params
    Then  expect combine(10, 15, 17) == 42

## Feature: Error Postconditions

## out_err Contract

    Tests postconditions for error cases.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | parses error postcondition | pass |
| 2 | validates success and error postconditions | pass |

**Example:** parses error postcondition
    Then  expect divide_safe(84, 2) == 42

**Example:** validates success and error postconditions
    Then  expect validate_age(21) == true

## Feature: Complex Contract Scenarios

## Advanced Contract Usage

    Tests complex contract combinations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates nested old expressions | pass |
| 2 | validates arithmetic contracts | pass |
| 3 | validates comparison chain contracts | pass |

**Example:** validates nested old expressions
    Then  expect complex_math(10, 11) == 42

**Example:** validates arithmetic contracts
    Then  expect increment_by_ten(32) == 42

**Example:** validates comparison chain contracts
    Then  expect clamp(42, 0, 100) == 42
    Then  expect clamp(200, 0, 100) == 100
    Then  expect clamp(-10, 0, 100) == 0

## Feature: All Contract Types Together

## Complete Contract Specification

    Tests functions with all contract types.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates full contract | pass |

**Example:** validates full contract
    Then  expect full_contract(20, 22) == 42

## Feature: Contract with Boolean Logic

## Boolean Contract Expressions

    Tests contracts using boolean operators.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates boolean logic contract | pass |
| 2 | validates negation contract | pass |

**Example:** validates boolean logic contract
    Then  expect validate_range(10, 20) == true

**Example:** validates negation contract
    Then  expect ensure_nonzero(42) == 42

## Feature: Contract with Conditionals

## Contracts in Branching Code

    Tests contracts work with conditional logic.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | validates conditional contract | pass |
| 2 | validates early return contract | pass |

**Example:** validates conditional contract
    Then  expect abs_with_contract(-42) == 42

**Example:** validates early return contract
    Then  expect early_exit(0) == 1
    Then  expect early_exit(42) == 42

## Feature: old() with Arithmetic Expressions

## Arithmetic in old() Capture

    Tests old() capturing arithmetic expressions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | captures arithmetic in old() | pass |
| 2 | references parameter in postcondition | pass |

**Example:** captures arithmetic in old()
    Given val doubled = x * 2
    Then  expect double_and_increment(20) == 41

**Example:** references parameter in postcondition
    Then  expect sum_with_check(20, 22) == 42


