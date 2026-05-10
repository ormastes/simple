# Arithmetic Operators Specification
*Source:* `test/feature/usage/operators_arithmetic_spec.spl`
**Feature IDs:** #100-110  |  **Category:** Syntax  |  **Status:** Implemented

## Overview



use std.text.{NL}

## Overview

Arithmetic operators in Simple provide standard mathematical operations on numeric types
(Int and Float). The language supports binary operators (+, -, *, /, %, **, //), unary
negation (-), automatic type coercion between Int and Float, and special behaviors for
strings and arrays.

## Syntax

### Binary Operators

```simple
val sum = 2 + 3           # Addition: 5
val diff = 10 - 4         # Subtraction: 6
val product = 4 * 5       # Multiplication: 20
val quotient = 20 / 4     # Division: 5
val remainder = 17 % 5    # Modulo: 2
val power = 2 ** 8        # Exponentiation: 256
val floor_div = 17.fdiv(5) # Floor division: 3 (// is now parallel operator)
```

### Unary Operators

```simple
val neg = -42             # Negation: -42
val pos_to_neg = -(5 + 3) # Negate expression: -8
```

### Operator Precedence

```simple
2 + 3 * 4         # 14 (multiplication before addition)
(2 + 3) * 4       # 20 (parentheses override)
2 ** 3 ** 2       # 512 (right-associative: 2 ** (3 ** 2)
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| Binary Operators | Operators requiring two operands (+, -, *, /, %, **, //) |
| Unary Operators | Operators requiring one operand (-) |
| Precedence | Order of evaluation (** > *, /, %, // > +, -) |
| Associativity | Left-to-right except ** (right-to-left) |
| Type Coercion | Int + Float automatically promotes to Float |

## Behavior

- **Addition (+)**: Works on Int, Float, String (concatenation), Array (concatenation)
- **Subtraction (-)**: Works on Int, Float
- **Multiplication (*)**: Works on Int, Float, String repetition (String * Int)
- **Division (/)**: Always returns numeric result, errors on division by zero
- **Modulo (%)**: Integer remainder, errors on modulo by zero
- **Exponentiation (**)**: Power operator, right-associative, no negative Int exponents
- **Floor Division (//)**: Euclidean division, rounds toward negative infinity
- **Negation (-)**: Unary minus, negates numeric values

## Related Specifications

- [Type Inference](../type_inference/type_inference_spec.md) - Type deduction for expressions
- [Comparison Operators](../operators_comparison/operators_comparison_spec.md) - Relational operators
- [Bitwise Operators](../operators_bitwise/operators_bitwise_spec.md) - Bit manipulation

## Implementation Notes

**Parser:** `src/parser/src/expressions/binary.rs`
- Precedence climbing algorithm
- Right-associativity for exponentiation

**Interpreter:** `src/compiler/src/interpreter/expr/ops.rs`
- Runtime evaluation with type coercion
- Error handling for division by zero
- Special handling for String and Array types

**Performance:** Most operations compile to native CPU instructions. Type coercion adds
minimal overhead (single conversion per mixed-type expression).

## Examples

```simple
# Basic arithmetic
val x = 10 + 20          # 30
val y = 100 - 25         # 75
val z = 6 * 7            # 42

# Type coercion
val mixed = 10 + 3.5     # 13.5 (Int promoted to Float)
val result = 2.0 * 5     # 10.0 (Int promoted to Float)

# String operations
val greeting = "Hello" + " " + "World"  # "Hello World"
val repeated = "x" * 5                  # "xxxxx"

# Exponentiation
val squared = 5 ** 2     # 25
val cubed = 2 ** 3       # 8
```

## Feature: Arithmetic Operators - Addition

## Addition Operator (+)

    The addition operator performs numeric addition on Int and Float types,
    with automatic type promotion when mixing types.

### Scenario: with integers

### Scenario: Integer Addition

        Adding two integers produces an integer result.

        ```simple
        val sum = 2 + 3  # 5
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | adds positive integers | pass |
| 2 | adds negative integers | pass |
| 3 | adds zero | pass |
| 4 | adds large integers | pass |

**Example:** adds positive integers
    Given val result = 2 + 3
    Then  expect(result).to_equal(5)

**Example:** adds negative integers
    Given val result = -5 + (-3)
    Then  expect(result).to_equal(-8)

**Example:** adds zero
    Given val result = 42 + 0
    Then  expect(result).to_equal(42)

**Example:** adds large integers
    Given val result = 1000 + 2000
    Then  expect(result).to_equal(3000)

### Scenario: with floats

### Scenario: Float Addition

        Adding two floats produces a float result.

        ```simple
        val sum = 2.5 + 3.5  # 6.0
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | adds positive floats | pass |
| 2 | adds negative floats | pass |

**Example:** adds positive floats
    Given val result = 2.5 + 3.5
    Then  expect(result).to_equal(6.0)

**Example:** adds negative floats
    Given val result = -1.5 + (-2.5)
    Then  expect(result).to_equal(-4.0)

### Scenario: with mixed types

### Scenario: Mixed Type Addition

        Adding Int and Float promotes Int to Float.

        ```simple
        val sum = 10 + 3.5  # 13.5 (Float)
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | promotes int to float (int + float) | pass |
| 2 | promotes int to float (float + int) | pass |

**Example:** promotes int to float (int + float)
    Given val result = 10 + 3.5
    Then  expect(result).to_equal(13.5)

**Example:** promotes int to float (float + int)
    Given val result = 2.5 + 7
    Then  expect(result).to_equal(9.5)

## Feature: Arithmetic Operators - Subtraction

## Subtraction Operator (-)

    The subtraction operator performs numeric subtraction on Int and Float types.

### Scenario: with integers

### Scenario: Integer Subtraction

        Subtracting two integers produces an integer result.

        ```simple
        val diff = 10 - 3  # 7
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | subtracts positive integers | pass |
| 2 | subtracts resulting in negative | pass |
| 3 | subtracts zero | pass |

**Example:** subtracts positive integers
    Given val result = 10 - 3
    Then  expect(result).to_equal(7)

**Example:** subtracts resulting in negative
    Given val result = 3 - 10
    Then  expect(result).to_equal(-7)

**Example:** subtracts zero
    Given val result = 42 - 0
    Then  expect(result).to_equal(42)

### Scenario: with floats

### Scenario: Float Subtraction

        Subtracting two floats produces a float result.

| # | Example | Status |
|---|---------|--------|
| 1 | subtracts positive floats | pass |

**Example:** subtracts positive floats
    Given val result = 10.5 - 3.2
    Then  expect(result).to_equal(7.3)

### Scenario: with mixed types

### Scenario: Mixed Type Subtraction

        Subtracting Int and Float promotes Int to Float.

| # | Example | Status |
|---|---------|--------|
| 1 | promotes int to float (int - float) | pass |
| 2 | promotes int to float (float - int) | pass |

**Example:** promotes int to float (int - float)
    Given val result = 10 - 2.5
    Then  expect(result).to_equal(7.5)

**Example:** promotes int to float (float - int)
    Given val result = 10.5 - 3
    Then  expect(result).to_equal(7.5)

## Feature: Arithmetic Operators - Multiplication

## Multiplication Operator (*)

    The multiplication operator performs numeric multiplication on Int and Float types.

### Scenario: with integers

### Scenario: Integer Multiplication

        Multiplying two integers produces an integer result.

        ```simple
        val product = 4 * 5  # 20
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies positive integers | pass |
| 2 | multiplies by zero | pass |
| 3 | multiplies by one | pass |
| 4 | multiplies negative numbers | pass |
| 5 | multiplies two negatives | pass |

**Example:** multiplies positive integers
    Given val result = 4 * 5
    Then  expect(result).to_equal(20)

**Example:** multiplies by zero
    Given val result = 42 * 0
    Then  expect(result == 0).to_equal(true)

**Example:** multiplies by one
    Given val result = 42 * 1
    Then  expect(result).to_equal(42)

**Example:** multiplies negative numbers
    Given val result = -3 * 4
    Then  expect(result).to_equal(-12)

**Example:** multiplies two negatives
    Given val result = -3 * -4
    Then  expect(result).to_equal(12)

### Scenario: with floats

### Scenario: Float Multiplication

        Multiplying two floats produces a float result.

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies positive floats | pass |

**Example:** multiplies positive floats
    Given val result = 2.5 * 4.0
    Then  expect(result).to_equal(10.0)

### Scenario: with mixed types

### Scenario: Mixed Type Multiplication

        Multiplying Int and Float promotes Int to Float.

| # | Example | Status |
|---|---------|--------|
| 1 | promotes int to float (int * float) | pass |
| 2 | promotes int to float (float * int) | pass |

**Example:** promotes int to float (int * float)
    Given val result = 5 * 2.5
    Then  expect(result).to_equal(12.5)

**Example:** promotes int to float (float * int)
    Given val result = 3.5 * 2
    Then  expect(result).to_equal(7.0)

## Feature: Arithmetic Operators - Division

## Division Operator (/)

    The division operator performs numeric division on Int and Float types.
    Division by zero produces an error.

### Scenario: with integers

### Scenario: Integer Division

        Dividing two integers produces a numeric result.

        ```simple
        val quotient = 20 / 4  # 5
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | divides evenly | pass |
| 2 | divides with remainder | pass |
| 3 | divides one by itself | pass |

**Example:** divides evenly
    Given val result = 20 / 4
    Then  expect(result).to_equal(5)

**Example:** divides with remainder
    Given val result = 17 / 5
    Then  expect(result).to_equal(3)

**Example:** divides one by itself
    Given val result = 42 / 42
    Then  expect(result).to_equal(1)

### Scenario: with floats

### Scenario: Float Division

        Dividing floats produces a float result.

| # | Example | Status |
|---|---------|--------|
| 1 | divides floats | pass |

**Example:** divides floats
    Given val result = 10.0 / 4.0
    Then  expect(result).to_equal(2.5)

### Scenario: with mixed types

### Scenario: Mixed Type Division

        Dividing Int and Float promotes Int to Float.

| # | Example | Status |
|---|---------|--------|
| 1 | promotes int to float (int / float) | pass |
| 2 | promotes int to float (float / int) | pass |

**Example:** promotes int to float (int / float)
    Given val result = 10 / 4.0
    Then  expect(result).to_equal(2.5)

**Example:** promotes int to float (float / int)
    Given val result = 10.0 / 4
    Then  expect(result).to_equal(2.5)

## Feature: Arithmetic Operators - Modulo

## Modulo Operator (%)

    The modulo operator computes the remainder of integer division.

### Scenario: with positive integers

### Scenario: Positive Integer Modulo

        Modulo with positive integers returns the remainder.

        ```simple
        val remainder = 17 % 5  # 2
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | computes remainder | pass |
| 2 | returns zero for even division | pass |
| 3 | returns operand when divisor is larger | pass |

**Example:** computes remainder
    Given val result = 17 % 5
    Then  expect(result).to_equal(2)

**Example:** returns zero for even division
    Given val result = 20 % 4
    Then  expect(result == 0).to_equal(true)

**Example:** returns operand when divisor is larger
    Given val result = 3 % 5
    Then  expect(result).to_equal(3)

### Scenario: with negative integers

### Scenario: Negative Integer Modulo

        Modulo with negative integers follows language semantics.

| # | Example | Status |
|---|---------|--------|
| 1 | handles negative dividend | pass |
| 2 | handles negative divisor | pass |

**Example:** handles negative dividend
    Given val result = -17 % 5
    Then  expect(result).to_equal(-2)

**Example:** handles negative divisor
    Given val result = 17 % -5
    Then  expect(result).to_equal(2)

## Feature: Arithmetic Operators - Exponentiation

## Exponentiation Operator (**)

    The exponentiation operator raises a number to a power.
    Right-associative: 2 ** 3 ** 2 means 2 ** (3 ** 2).

### Scenario: with integers

### Scenario: Integer Exponentiation

        Raising an integer to an integer power.

        ```simple
        val squared = 5 ** 2  # 25
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | computes square | pass |
| 2 | computes cube | pass |
| 3 | computes power of zero | pass |
| 4 | computes power of one | pass |

**Example:** computes square
    Given val result = 5 ** 2
    Then  expect(result).to_equal(25)

**Example:** computes cube
    Given val result = 2 ** 3
    Then  expect(result).to_equal(8)

**Example:** computes power of zero
    Given val result = 42 ** 0
    Then  expect(result).to_equal(1)

**Example:** computes power of one
    Given val result = 42 ** 1
    Then  expect(result).to_equal(42)

### Scenario: with floats

### Scenario: Float Exponentiation

        Raising floats to powers.

| # | Example | Status |
|---|---------|--------|
| 1 | computes float power | pass |

**Example:** computes float power
    Given val result = 2.0 ** 3.0
    Then  expect(result).to_equal(8.0)

### Scenario: with right associativity

### Scenario: Right Associativity

        Exponentiation is right-associative.

        ```simple
        2 ** 3 ** 2  # 2 ** (3 ** 2) = 2 ** 9 = 512
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates right to left | pass |

**Example:** evaluates right to left
    Given val result = 2 ** 3 ** 2
    Then  expect(result).to_equal(512)

## Feature: Arithmetic Operators - Floor Division

## Floor Division Operator (//)

    Floor division divides and rounds toward negative infinity.
    Uses Euclidean division semantics.

### Scenario: with positive integers

### Scenario: Positive Floor Division

        Floor division with positive integers.

        ```simple
        val result = 17 // 5  # 3
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | divides and floors | pass |
| 2 | returns exact result for even division | pass |

**Example:** divides and floors
    Given val result = 17.fdiv(5)
    Then  expect(result).to_equal(3)

**Example:** returns exact result for even division
    Given val result = 20.fdiv(4)
    Then  expect(result).to_equal(5)

## Feature: Arithmetic Operators - Unary Negation

## Unary Negation Operator (-)

    The unary minus operator negates a numeric value.

### Scenario: with integers

### Scenario: Integer Negation

        Negating an integer produces its opposite.

        ```simple
        val neg = -42  # -42
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | negates positive integer | pass |
| 2 | negates negative integer | pass |
| 3 | negates zero | pass |

**Example:** negates positive integer
    Given val result = -42
    Then  expect(result).to_equal(-42)

**Example:** negates negative integer
    Given val x = -42
    Given val result = -x
    Then  expect(result).to_equal(42)

**Example:** negates zero
    Given val result = -0
    Then  expect(result == 0).to_equal(true)

### Scenario: with floats

### Scenario: Float Negation

        Negating a float produces its opposite.

| # | Example | Status |
|---|---------|--------|
| 1 | negates positive float | pass |

**Example:** negates positive float
    Given val result = -3.5
    Then  expect(result).to_equal(-3.5)

### Scenario: with expressions

### Scenario: Expression Negation

        Negating an expression.

        ```simple
        val neg = -(5 + 3)  # -8
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | negates expression result | pass |

**Example:** negates expression result
    Given val result = -(5 + 3)
    Then  expect(result).to_equal(-8)

## Feature: Arithmetic Operators - Precedence

## Operator Precedence

    Operators are evaluated in precedence order:
    1. ** (exponentiation)
    2. *, /, % (multiplication, division, modulo)
    3. +, - (addition, subtraction)

    Note: Floor division is now a method (.fdiv), not an operator.
    The // operator is now used for parallel execution.

### Scenario: multiplication before addition

### Scenario: Multiplication Precedence

        Multiplication has higher precedence than addition.

        ```simple
        2 + 3 * 4  # 14, not 20
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates multiplication first | pass |
| 2 | uses parentheses to override | pass |

**Example:** evaluates multiplication first
    Given val result = 2 + 3 * 4
    Then  expect(result).to_equal(14)

**Example:** uses parentheses to override
    Given val result = (2 + 3) * 4
    Then  expect(result).to_equal(20)

### Scenario: exponentiation before multiplication

### Scenario: Exponentiation Precedence

        Exponentiation has higher precedence than multiplication.

        ```simple
        2 * 3 ** 2  # 18, not 36
        ```

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates exponentiation first | pass |
| 2 | uses parentheses to override | pass |

**Example:** evaluates exponentiation first
    Given val result = 2 * 3 ** 2
    Then  expect(result).to_equal(18)

**Example:** uses parentheses to override
    Given val result = (2 * 3) ** 2
    Then  expect(result).to_equal(36)

### Scenario: complex expressions

### Scenario: Complex Precedence

        Multiple operators with different precedence.

| # | Example | Status |
|---|---------|--------|
| 1 | evaluates complex expression correctly | pass |
| 2 | evaluates with division | pass |

**Example:** evaluates complex expression correctly
    Given val result = 2 + 3 * 4 - 5
    Then  expect(result).to_equal(9)

**Example:** evaluates with division
    Given val result = 20 / 4 + 3 * 2
    Then  expect(result).to_equal(11)

## Feature: Arithmetic Operators - Type Coercion

## Automatic Type Coercion

    When mixing Int and Float in arithmetic operations, Int is automatically
    promoted to Float, and the result is Float.

### Scenario: in complex expressions

### Scenario: Mixed Type Expressions

        Complex expressions with mixed Int and Float types.

| # | Example | Status |
|---|---------|--------|
| 1 | promotes in nested expressions | pass |
| 2 | promotes across multiple operations | pass |

**Example:** promotes in nested expressions
    Given val result = 10 + 5 * 2.0
    Then  expect(result).to_equal(20.0)

**Example:** promotes across multiple operations
    Given val result = 1 + 2 + 3.0
    Then  expect(result).to_equal(6.0)

## Feature: Arithmetic Operators - Edge Cases

## Edge Case Handling

    Tests for special cases and boundaries.

### Scenario: with zero

### Scenario: Operations with Zero

        Zero has special properties in arithmetic.

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies by zero | pass |
| 2 | adds zero (identity) | pass |

**Example:** multiplies by zero
    Given val result = 42 * 0
    Then  expect(result == 0).to_equal(true)

**Example:** adds zero (identity)
    Given val result = 42 + 0
    Then  expect(result).to_equal(42)

### Scenario: with one

### Scenario: Operations with One

        One is the multiplicative identity.

| # | Example | Status |
|---|---------|--------|
| 1 | multiplies by one | pass |
| 2 | divides by one | pass |
| 3 | raises to power of zero | pass |

**Example:** multiplies by one
    Given val result = 42 * 1
    Then  expect(result).to_equal(42)

**Example:** divides by one
    Given val result = 42 / 1
    Then  expect(result).to_equal(42)

**Example:** raises to power of zero
    Given val result = 42 ** 0
    Then  expect(result).to_equal(1)


