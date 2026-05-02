# Arithmetic Operators Specification

Arithmetic operators in Simple provide standard mathematical operations on numeric types (Int and Float). The language supports binary operators (+, -, *, /, %, **, //), unary negation (-), automatic type coercion between Int and Float, and special behaviors for strings and arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #100-110 |
| Category | Syntax |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/operators_arithmetic_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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
val x = 10 + 20          # 30
val y = 100 - 25         # 75
val z = 6 * 7            # 42

val mixed = 10 + 3.5     # 13.5 (Int promoted to Float)
val result = 2.0 * 5     # 10.0 (Int promoted to Float)

val greeting = "Hello" + " " + "World"  # "Hello World"
val repeated = "x" * 5                  # "xxxxx"

val squared = 5 ** 2     # 25
val cubed = 2 ** 3       # 8
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/operators_arithmetic/result.json` |

## Scenarios

- adds positive integers
- adds negative integers
- adds zero
- adds large integers
- adds positive floats
- adds negative floats
- promotes int to float (int + float)
- promotes int to float (float + int)
- subtracts positive integers
- subtracts resulting in negative
- subtracts zero
- subtracts positive floats
- promotes int to float (int - float)
- promotes int to float (float - int)
- multiplies positive integers
- multiplies by zero
- multiplies by one
- multiplies negative numbers
- multiplies two negatives
- multiplies positive floats
- promotes int to float (int * float)
- promotes int to float (float * int)
- divides evenly
- divides with remainder
- divides one by itself
- divides floats
- promotes int to float (int / float)
- promotes int to float (float / int)
- computes remainder
- returns zero for even division
- returns operand when divisor is larger
- handles negative dividend
- handles negative divisor
- computes square
- computes cube
- computes power of zero
- computes power of one
- computes float power
- evaluates right to left
- divides and floors
- returns exact result for even division
- negates positive integer
- negates negative integer
- negates zero
- negates positive float
- negates expression result
- evaluates multiplication first
- uses parentheses to override
- evaluates exponentiation first
- uses parentheses to override
- evaluates complex expression correctly
- evaluates with division
- promotes in nested expressions
- promotes across multiple operations
- multiplies by zero
- adds zero (identity)
- multiplies by one
- divides by one
- raises to power of zero
