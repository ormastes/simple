# Arithmetic Operators Specification

**Feature ID:** #100-110 | **Category:** Syntax | **Difficulty:** 2/5 | **Status:** Implemented

_Source: `test/feature/usage/operators_arithmetic_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 59 |

## Test Structure

### Arithmetic Operators - Addition

#### with integers

- ✅ adds positive integers
- ✅ adds negative integers
- ✅ adds zero
- ✅ adds large integers
#### with floats

- ✅ adds positive floats
- ✅ adds negative floats
#### with mixed types

- ✅ promotes int to float (int + float)
- ✅ promotes int to float (float + int)
### Arithmetic Operators - Subtraction

#### with integers

- ✅ subtracts positive integers
- ✅ subtracts resulting in negative
- ✅ subtracts zero
#### with floats

- ✅ subtracts positive floats
#### with mixed types

- ✅ promotes int to float (int - float)
- ✅ promotes int to float (float - int)
### Arithmetic Operators - Multiplication

#### with integers

- ✅ multiplies positive integers
- ✅ multiplies by zero
- ✅ multiplies by one
- ✅ multiplies negative numbers
- ✅ multiplies two negatives
#### with floats

- ✅ multiplies positive floats
#### with mixed types

- ✅ promotes int to float (int * float)
- ✅ promotes int to float (float * int)
### Arithmetic Operators - Division

#### with integers

- ✅ divides evenly
- ✅ divides with remainder
- ✅ divides one by itself
#### with floats

- ✅ divides floats
#### with mixed types

- ✅ promotes int to float (int / float)
- ✅ promotes int to float (float / int)
### Arithmetic Operators - Modulo

#### with positive integers

- ✅ computes remainder
- ✅ returns zero for even division
- ✅ returns operand when divisor is larger
#### with negative integers

- ✅ handles negative dividend
- ✅ handles negative divisor
### Arithmetic Operators - Exponentiation

#### with integers

- ✅ computes square
- ✅ computes cube
- ✅ computes power of zero
- ✅ computes power of one
#### with floats

- ✅ computes float power
#### with right associativity

- ✅ evaluates right to left
### Arithmetic Operators - Floor Division

#### with positive integers

- ✅ divides and floors
- ✅ returns exact result for even division
### Arithmetic Operators - Unary Negation

#### with integers

- ✅ negates positive integer
- ✅ negates negative integer
- ✅ negates zero
#### with floats

- ✅ negates positive float
#### with expressions

- ✅ negates expression result
### Arithmetic Operators - Precedence

#### multiplication before addition

- ✅ evaluates multiplication first
- ✅ uses parentheses to override
#### exponentiation before multiplication

- ✅ evaluates exponentiation first
- ✅ uses parentheses to override
#### complex expressions

- ✅ evaluates complex expression correctly
- ✅ evaluates with division
### Arithmetic Operators - Type Coercion

#### in complex expressions

- ✅ promotes in nested expressions
- ✅ promotes across multiple operations
### Arithmetic Operators - Edge Cases

#### with zero

- ✅ multiplies by zero
- ✅ adds zero (identity)
#### with one

- ✅ multiplies by one
- ✅ divides by one
- ✅ raises to power of zero

