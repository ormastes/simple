# Math Block Tensor Operations Specification
*Source:* `test/feature/usage/math_blocks_spec.spl`
**Feature IDs:** #1090-1098 (subset: tensor ops)  |  **Category:** Syntax / Math DSL  |  **Status:** Implemented

## Overview



## Overview

The `m{}` math block supports torch-compatible tensor operations for numerical computing.
Each math block is a self-contained DSL expression that returns a Block value.

## Feature: Math Block Arithmetic

Basic arithmetic operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates addition | pass |
| 2 | evaluates subtraction | pass |
| 3 | evaluates multiplication | pass |
| 4 | evaluates division | pass |
| 5 | evaluates complex expression | pass |
| 6 | respects operator precedence | pass |
| 7 | evaluates power | pass |
| 8 | evaluates negative numbers | pass |

**Example:** evaluates addition
    Given val result = m{ 2 + 3 }
    Then  expect(result).to_equal(5)

**Example:** evaluates subtraction
    Given val result = m{ 10 - 3 }
    Then  expect(result).to_equal(7)

**Example:** evaluates multiplication
    Given val result = m{ 4 * 5 }
    Then  expect(result).to_equal(20)

**Example:** evaluates division
    Given val result = m{ 15 / 3 }
    Then  expect(result).to_equal(5)

**Example:** evaluates complex expression
    Given val result = m{ (2 + 3) * 4 }
    Then  expect(result).to_equal(20)

**Example:** respects operator precedence
    Given val result = m{ 2 + 3 * 4 }
    Then  expect(result).to_equal(14)

**Example:** evaluates power
    Given val result = m{ 2^3 }
    Then  expect(result).to_equal(8.0)

**Example:** evaluates negative numbers
    Given val result = m{ -5 + 3 }
    Then  expect(result).to_equal(-2)

## Feature: Math Block Functions

Built-in math functions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates sqrt of 16 | pass |
| 2 | evaluates sqrt of 9 | pass |
| 3 | evaluates abs of negative | pass |
| 4 | evaluates abs of positive | pass |
| 5 | evaluates frac | pass |
| 6 | evaluates nested functions | pass |

**Example:** evaluates sqrt of 16
    Given val result = m{ sqrt(16) }
    Then  expect(result).to_equal(4.0)

**Example:** evaluates sqrt of 9
    Given val result = m{ sqrt(9) }
    Then  expect(result).to_equal(3.0)

**Example:** evaluates abs of negative
    Given val result = m{ abs(-5) }
    Then  expect(result).to_equal(5)

**Example:** evaluates abs of positive
    Given val result = m{ abs(7) }
    Then  expect(result).to_equal(7)

**Example:** evaluates frac
    Given val result = m{ frac(6, 2) }
    Then  expect(result).to_equal(3.0)

**Example:** evaluates nested functions
    Given val result = m{ sqrt(abs(-16)) }
    Then  expect(result).to_equal(4.0)

## Feature: Math Block Matrix Operations

Matrix operations that produce scalar results.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | computes dot product | pass |
| 2 | computes dot product simple | pass |

**Example:** computes dot product
    Given val result = m{ dot([1, 2, 3], [4, 5, 6]) }
    Then  expect(result).to_equal(32.0)

**Example:** computes dot product simple
    Given val result = m{ dot([1, 1], [2, 2]) }
    Then  expect(result).to_equal(4.0)

## Feature: Math Block Constants

Built-in math constants.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates pi greater than 3 | pass |
| 2 | evaluates pi less than 4 | pass |
| 3 | evaluates e greater than 2 | pass |
| 4 | evaluates e less than 3 | pass |

**Example:** evaluates pi greater than 3
    Given val result = m{ pi }
    Then  expect(result).to_be_greater_than(3.0)

**Example:** evaluates pi less than 4
    Given val result = m{ pi }
    Then  expect(result).to_be_less_than(4.0)

**Example:** evaluates e greater than 2
    Given val result = m{ e }
    Then  expect(result).to_be_greater_than(2.0)

**Example:** evaluates e less than 3
    Given val result = m{ e }
    Then  expect(result).to_be_less_than(3.0)

## Feature: Math Block Array Expressions

Array expressions that produce scalar results through reductions.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates array subscript | pass |
| 2 | evaluates nested array subscript | pass |

**Example:** evaluates array subscript
    Given val result = m{ [10, 20, 30][1] }
    Then  expect(result).to_equal(20.0)

**Example:** evaluates nested array subscript
    Given val result = m{ [[1, 2], [3, 4]][0][1] }
    Then  expect(result).to_equal(2.0)

## Feature: Math Block LaTeX Compatibility

LaTeX-style syntax support (with deprecation warnings).

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates LaTeX frac | pass |
| 2 | evaluates LaTeX sqrt | pass |
| 3 | evaluates Greek letter pi | pass |

**Example:** evaluates LaTeX frac
    Given val result = m{ \frac{10}{2} }
    Then  expect(result).to_equal(5.0)

**Example:** evaluates LaTeX sqrt
    Given val result = m{ \sqrt{25} }
    Then  expect(result).to_equal(5.0)

**Example:** evaluates Greek letter pi
    Given val result = m{ \pi }
    Then  expect(result).to_be_greater_than(3.0)

## Feature: Math Block LaTeX Export

Math expressions can be exported to LaTeX format.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | exports simple arithmetic | pass |
| 2 | exports fractions | pass |
| 3 | exports Greek letters | pass |

**Example:** exports simple arithmetic
    Given val result = m{ 2 + 3 }
    Then  expect(result).to_equal(5)

**Example:** exports fractions
    Given val result = m{ frac(1, 2) }
    Then  expect(result).to_equal(0.5)

**Example:** exports Greek letters
    Given val result = m{ pi }
    Then  expect(result).to_be_greater_than(3.0)


