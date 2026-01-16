*Source: `simple/test/system/features/operators_arithmetic/operators_arithmetic_spec.spl`*
*Last Updated: 2026-01-16*

---

# Arithmetic Operators Specification

**Feature IDs:** #100-110
**Category:** Syntax
**Difficulty:** 2/5
**Status:** Implemented

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
val floor_div = 17 // 5   # Floor division: 3
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
2 ** 3 ** 2       # 512 (right-associative: 2 ** (3 ** 2))
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

## Addition Operator (+)

    The addition operator performs numeric addition on Int and Float types,
    with automatic type promotion when mixing types.

### Scenario: Integer Addition

        Adding two integers produces an integer result.

        ```simple
        val sum = 2 + 3  # 5
        ```

### Scenario: Float Addition

        Adding two floats produces a float result.

        ```simple
        val sum = 2.5 + 3.5  # 6.0
        ```

### Scenario: Mixed Type Addition

        Adding Int and Float promotes Int to Float.

        ```simple
        val sum = 10 + 3.5  # 13.5 (Float)
        ```

## Subtraction Operator (-)

    The subtraction operator performs numeric subtraction on Int and Float types.

### Scenario: Integer Subtraction

        Subtracting two integers produces an integer result.

        ```simple
        val diff = 10 - 3  # 7
        ```

### Scenario: Float Subtraction

        Subtracting two floats produces a float result.

### Scenario: Mixed Type Subtraction

        Subtracting Int and Float promotes Int to Float.

## Multiplication Operator (*)

    The multiplication operator performs numeric multiplication on Int and Float types.

### Scenario: Integer Multiplication

        Multiplying two integers produces an integer result.

        ```simple
        val product = 4 * 5  # 20
        ```

### Scenario: Float Multiplication

        Multiplying two floats produces a float result.

### Scenario: Mixed Type Multiplication

        Multiplying Int and Float promotes Int to Float.

## Division Operator (/)

    The division operator performs numeric division on Int and Float types.
    Division by zero produces an error.

### Scenario: Integer Division

        Dividing two integers produces a numeric result.

        ```simple
        val quotient = 20 / 4  # 5
        ```

### Scenario: Float Division

        Dividing floats produces a float result.

### Scenario: Mixed Type Division

        Dividing Int and Float promotes Int to Float.

## Modulo Operator (%)

    The modulo operator computes the remainder of integer division.

### Scenario: Positive Integer Modulo

        Modulo with positive integers returns the remainder.

        ```simple
        val remainder = 17 % 5  # 2
        ```

### Scenario: Negative Integer Modulo

        Modulo with negative integers follows language semantics.

## Exponentiation Operator (**)

    The exponentiation operator raises a number to a power.
    Right-associative: 2 ** 3 ** 2 means 2 ** (3 ** 2).

### Scenario: Integer Exponentiation

        Raising an integer to an integer power.

        ```simple
        val squared = 5 ** 2  # 25
        ```

### Scenario: Float Exponentiation

        Raising floats to powers.

### Scenario: Right Associativity

        Exponentiation is right-associative.

        ```simple
        2 ** 3 ** 2  # 2 ** (3 ** 2) = 2 ** 9 = 512
        ```

## Floor Division Operator (//)

    Floor division divides and rounds toward negative infinity.
    Uses Euclidean division semantics.

### Scenario: Positive Floor Division

        Floor division with positive integers.

        ```simple
        val result = 17 // 5  # 3
        ```

## Unary Negation Operator (-)

    The unary minus operator negates a numeric value.

### Scenario: Integer Negation

        Negating an integer produces its opposite.

        ```simple
        val neg = -42  # -42
        ```

### Scenario: Float Negation

        Negating a float produces its opposite.

### Scenario: Expression Negation

        Negating an expression.

        ```simple
        val neg = -(5 + 3)  # -8
        ```

## Operator Precedence

    Operators are evaluated in precedence order:
    1. ** (exponentiation)
    2. *, /, %, // (multiplication, division, modulo, floor division)
    3. +, - (addition, subtraction)

### Scenario: Multiplication Precedence

        Multiplication has higher precedence than addition.

        ```simple
        2 + 3 * 4  # 14, not 20
        ```

### Scenario: Exponentiation Precedence

        Exponentiation has higher precedence than multiplication.

        ```simple
        2 * 3 ** 2  # 18, not 36
        ```

### Scenario: Complex Precedence

        Multiple operators with different precedence.

## Automatic Type Coercion

    When mixing Int and Float in arithmetic operations, Int is automatically
    promoted to Float, and the result is Float.

### Scenario: Mixed Type Expressions

        Complex expressions with mixed Int and Float types.

## Edge Case Handling

    Tests for special cases and boundaries.

### Scenario: Operations with Zero

        Zero has special properties in arithmetic.

### Scenario: Operations with One

        One is the multiplicative identity.
