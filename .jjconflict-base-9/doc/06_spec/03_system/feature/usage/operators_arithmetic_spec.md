# Arithmetic Operators Specification

> Arithmetic operators in Simple provide standard mathematical operations on numeric types (Int and Float). The language supports binary operators (+, -, *, /, %, **, //), unary negation (-), automatic type coercion between Int and Float, and special behaviors for strings and arrays.

<!-- sdn-diagram:id=operators_arithmetic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=operators_arithmetic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

operators_arithmetic_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=operators_arithmetic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 59 | 59 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arithmetic Operators Specification

Arithmetic operators in Simple provide standard mathematical operations on numeric types (Int and Float). The language supports binary operators (+, -, *, /, %, **, //), unary negation (-), automatic type coercion between Int and Float, and special behaviors for strings and arrays.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #100-110 |
| Category | Syntax |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/operators_arithmetic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

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

## Scenarios

### Arithmetic Operators - Addition

#### with integers

#### adds positive integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3
expect(result).to_equal(5)
```

</details>

#### adds negative integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -5 + (-3)
expect(result).to_equal(-8)
```

</details>

#### adds zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 + 0
expect(result).to_equal(42)
```

</details>

#### adds large integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1000 + 2000
expect(result).to_equal(3000)
```

</details>

#### with floats

#### adds positive floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.5 + 3.5
expect(result).to_equal(6.0)
```

</details>

#### adds negative floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -1.5 + (-2.5)
expect(result).to_equal(-4.0)
```

</details>

#### with mixed types

#### promotes int to float (int + float)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + 3.5
expect(result).to_equal(13.5)
```

</details>

#### promotes int to float (float + int)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.5 + 7
expect(result).to_equal(9.5)
```

</details>

### Arithmetic Operators - Subtraction

#### with integers

#### subtracts positive integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 - 3
expect(result).to_equal(7)
```

</details>

#### subtracts resulting in negative

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 3 - 10
expect(result).to_equal(-7)
```

</details>

#### subtracts zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 - 0
expect(result).to_equal(42)
```

</details>

#### with floats

#### subtracts positive floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10.5 - 3.2
expect(result).to_equal(7.3)
```

</details>

#### with mixed types

#### promotes int to float (int - float)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 - 2.5
expect(result).to_equal(7.5)
```

</details>

#### promotes int to float (float - int)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10.5 - 3
expect(result).to_equal(7.5)
```

</details>

### Arithmetic Operators - Multiplication

#### with integers

#### multiplies positive integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 4 * 5
expect(result).to_equal(20)
```

</details>

#### multiplies by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 * 0
expect(result == 0).to_equal(true)
```

</details>

#### multiplies by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 * 1
expect(result).to_equal(42)
```

</details>

#### multiplies negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -3 * 4
expect(result).to_equal(-12)
```

</details>

#### multiplies two negatives

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -3 * -4
expect(result).to_equal(12)
```

</details>

#### with floats

#### multiplies positive floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.5 * 4.0
expect(result).to_equal(10.0)
```

</details>

#### with mixed types

#### promotes int to float (int * float)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 * 2.5
expect(result).to_equal(12.5)
```

</details>

#### promotes int to float (float * int)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 3.5 * 2
expect(result).to_equal(7.0)
```

</details>

### Arithmetic Operators - Division

#### with integers

#### divides evenly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 20 / 4
expect(result).to_equal(5)
```

</details>

#### divides with remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 17 / 5
expect(result).to_equal(3)
```

</details>

#### divides one by itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 / 42
expect(result).to_equal(1)
```

</details>

#### with floats

#### divides floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10.0 / 4.0
expect(result).to_equal(2.5)
```

</details>

#### with mixed types

#### promotes int to float (int / float)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 / 4.0
expect(result).to_equal(2.5)
```

</details>

#### promotes int to float (float / int)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10.0 / 4
expect(result).to_equal(2.5)
```

</details>

### Arithmetic Operators - Modulo

#### with positive integers

#### computes remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 17 % 5
expect(result).to_equal(2)
```

</details>

#### returns zero for even division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 20 % 4
expect(result == 0).to_equal(true)
```

</details>

#### returns operand when divisor is larger

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 3 % 5
expect(result).to_equal(3)
```

</details>

#### with negative integers

#### handles negative dividend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -17 % 5
expect(result).to_equal(-2)
```

</details>

#### handles negative divisor

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 17 % -5
expect(result).to_equal(2)
```

</details>

### Arithmetic Operators - Exponentiation

#### with integers

#### computes square

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 5 ** 2
expect(result).to_equal(25)
```

</details>

#### computes cube

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 ** 3
expect(result).to_equal(8)
```

</details>

#### computes power of zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 ** 0
expect(result).to_equal(1)
```

</details>

#### computes power of one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 ** 1
expect(result).to_equal(42)
```

</details>

#### with floats

#### computes float power

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2.0 ** 3.0
expect(result).to_equal(8.0)
```

</details>

#### with right associativity

#### evaluates right to left

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 ** 3 ** 2
expect(result).to_equal(512)
```

</details>

### Arithmetic Operators - Floor Division

#### with positive integers

#### divides and floors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 17.fdiv(5)
expect(result).to_equal(3)
```

</details>

#### returns exact result for even division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 20.fdiv(4)
expect(result).to_equal(5)
```

</details>

### Arithmetic Operators - Unary Negation

#### with integers

#### negates positive integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -42
expect(result).to_equal(-42)
```

</details>

#### negates negative integer

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -42
val result = -x
expect(result).to_equal(42)
```

</details>

#### negates zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -0
expect(result == 0).to_equal(true)
```

</details>

#### with floats

#### negates positive float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -3.5
expect(result).to_equal(-3.5)
```

</details>

#### with expressions

#### negates expression result

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -(5 + 3)
expect(result).to_equal(-8)
```

</details>

### Arithmetic Operators - Precedence

#### multiplication before addition

#### evaluates multiplication first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3 * 4
expect(result).to_equal(14)
```

</details>

#### uses parentheses to override

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (2 + 3) * 4
expect(result).to_equal(20)
```

</details>

#### exponentiation before multiplication

#### evaluates exponentiation first

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 * 3 ** 2
expect(result).to_equal(18)
```

</details>

#### uses parentheses to override

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (2 * 3) ** 2
expect(result).to_equal(36)
```

</details>

#### complex expressions

#### evaluates complex expression correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3 * 4 - 5
expect(result).to_equal(9)
```

</details>

#### evaluates with division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 20 / 4 + 3 * 2
expect(result).to_equal(11)
```

</details>

### Arithmetic Operators - Type Coercion

#### in complex expressions

#### promotes in nested expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 10 + 5 * 2.0
expect(result).to_equal(20.0)
```

</details>

#### promotes across multiple operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 + 2 + 3.0
expect(result).to_equal(6.0)
```

</details>

### Arithmetic Operators - Edge Cases

#### with zero

#### multiplies by zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 * 0
expect(result == 0).to_equal(true)
```

</details>

#### adds zero (identity)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 + 0
expect(result).to_equal(42)
```

</details>

#### with one

#### multiplies by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 * 1
expect(result).to_equal(42)
```

</details>

#### divides by one

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 / 1
expect(result).to_equal(42)
```

</details>

#### raises to power of zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42 ** 0
expect(result).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
