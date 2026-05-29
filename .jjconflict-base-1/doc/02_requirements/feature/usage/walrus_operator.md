# walrus operator
*Source:* `test/feature/usage/walrus_operator_spec.spl`

## Feature: Walrus Operator Basics

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates binding with integer | pass |
| 2 | creates binding with text | pass |
| 3 | creates binding with boolean | pass |
| 4 | creates binding with nil | pass |
| 5 | creates binding with float | pass |

**Example:** creates binding with integer
    Then  expect(x).to_equal(42)

**Example:** creates binding with text
    Then  expect(name).to_equal("Alice")

**Example:** creates binding with boolean
    Then  expect(flag).to_equal(true)

**Example:** creates binding with nil
    Then  expect(value).to_be_nil()

**Example:** creates binding with float
    Then  expect(pi).to_equal(3.14)

## Feature: Walrus Operator with Expressions

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates expression on right side | pass |
| 2 | works with function calls | pass |
| 3 | works with string concatenation | pass |
| 4 | works with arrays | pass |

**Example:** evaluates expression on right side
    Then  expect(result).to_equal(42)

**Example:** works with function calls
    Then  expect(val_from_fn).to_equal(100)

**Example:** works with string concatenation
    Then  expect(greeting).to_equal("Hello World")

**Example:** works with arrays
    Then  expect(numbers.len()).to_equal(3)
    Then  expect(numbers[0]).to_equal(1)

## Feature: Walrus Operator Semantics

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates immutable binding | pass |
| 2 | is equivalent to val declaration | pass |
| 3 | works in nested scopes | pass |

**Example:** creates immutable binding
    Then  expect(count).to_equal(5)

**Example:** is equivalent to val declaration
    Given val y = 10
    Then  expect(x).to_equal(y)

**Example:** works in nested scopes
    Then  expect(outer()).to_equal(300)

## Feature: Walrus Operator in Functions

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works in function body | pass |
| 2 | works with multiple bindings | pass |
| 3 | works with shadowing in nested scopes | pass |

**Example:** works in function body
    Then  expect(test_walrus()).to_equal(42)

**Example:** works with multiple bindings
    Then  expect(multi_walrus()).to_equal(6)

**Example:** works with shadowing in nested scopes
    Then  expect(inner()).to_equal(20)
    Then  expect(outer_x).to_equal(10)

## Feature: Walrus Operator in Control Flow

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works in if branches | pass |
| 2 | works in loops | pass |
| 3 | works in match cases | pass |

**Example:** works in if branches
    Then  expect(val_in_if).to_equal(42)

**Example:** works in loops
    Given var sum = 0
    Then  expect(sum).to_equal(20)

**Example:** works in match cases
    Given val value = 42
    Given var result = 0
    Then  expect(result).to_equal(100)

## Feature: Walrus Operator with Complex Types

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | works with nested arrays | pass |
| 2 | works with struct literals | pass |

**Example:** works with nested arrays
    Then  expect(matrix.len()).to_equal(2)
    Then  expect(matrix[0][0]).to_equal(1)

**Example:** works with struct literals
    Then  expect(point.x).to_equal(10)
    Then  expect(point.y).to_equal(20)

## Feature: Walrus Operator Edge Cases

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles parenthesized expressions | pass |
| 2 | handles chained operations | pass |
| 3 | handles boolean expressions | pass |

**Example:** handles parenthesized expressions
    Then  expect(val_paren).to_equal(30)

**Example:** handles chained operations
    Then  expect(chained).to_equal(10)

**Example:** handles boolean expressions
    Then  expect(is_true).to_equal(true)
    Then  expect(is_false).to_equal(false)

## Feature: Walrus vs Regular Assignment

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | walrus creates new binding | pass |
| 2 | regular assignment requires val/var | pass |

**Example:** walrus creates new binding
    Then  expect(x).to_equal(10)

**Example:** regular assignment requires val/var
    Given val y = 20
    Then  expect(y).to_equal(20)


