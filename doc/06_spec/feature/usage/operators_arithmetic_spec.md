# Arithmetic Operators Specification

> Arithmetic operators in Simple provide standard mathematical operations on numeric types (Int and Float). The language supports binary operators (+, -, *, /, %, **, //), unary negation (-), automatic type coercion between Int and Float, and special behaviors for strings and arrays.

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
| Source | `test/feature/usage/operators_arithmetic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Arithmetic operators in Simple provide standard mathematical operations on numeric types
(Int and Float). The language supports binary operators (+, -, *, /, %, **, //), unary
negation (-), automatic type coercion between Int and Float, and special behaviors for
strings and arrays.

## Syntax

### Binary Operators

```simple
use std.spec.step

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

- adds positive integers
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds positive integers")
val result = 2 + 3
expect(result).to_equal(5)
```

</details>

#### adds negative integers

- adds negative integers
   - Expected: result equals `-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds negative integers")
val result = -5 + (-3)
expect(result).to_equal(-8)
```

</details>

#### adds zero

- adds zero
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds zero")
val result = 42 + 0
expect(result).to_equal(42)
```

</details>

#### adds large integers

- adds large integers
   - Expected: result equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds large integers")
val result = 1000 + 2000
expect(result).to_equal(3000)
```

</details>

#### with floats

#### adds positive floats

- adds positive floats
   - Expected: result equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds positive floats")
val result = 2.5 + 3.5
expect(result).to_equal(6.0)
```

</details>

#### adds negative floats

- adds negative floats
   - Expected: result equals `-4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds negative floats")
val result = -1.5 + (-2.5)
expect(result).to_equal(-4.0)
```

</details>

#### with mixed types

#### promotes int to float (int + float)

- promotes int to float (int + float)
   - Expected: result equals `13.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (int + float)")
val result = 10 + 3.5
expect(result).to_equal(13.5)
```

</details>

#### promotes int to float (float + int)

- promotes int to float (float + int)
   - Expected: result equals `9.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (float + int)")
val result = 2.5 + 7
expect(result).to_equal(9.5)
```

</details>

### Arithmetic Operators - Subtraction

#### with integers

#### subtracts positive integers

- subtracts positive integers
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts positive integers")
val result = 10 - 3
expect(result).to_equal(7)
```

</details>

#### subtracts resulting in negative

- subtracts resulting in negative
   - Expected: result equals `-7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts resulting in negative")
val result = 3 - 10
expect(result).to_equal(-7)
```

</details>

#### subtracts zero

- subtracts zero
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts zero")
val result = 42 - 0
expect(result).to_equal(42)
```

</details>

#### with floats

#### subtracts positive floats

- subtracts positive floats
   - Expected: result equals `7.3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("subtracts positive floats")
val result = 10.5 - 3.2
expect(result).to_equal(7.3)
```

</details>

#### with mixed types

#### promotes int to float (int - float)

- promotes int to float (int - float)
   - Expected: result equals `7.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (int - float)")
val result = 10 - 2.5
expect(result).to_equal(7.5)
```

</details>

#### promotes int to float (float - int)

- promotes int to float (float - int)
   - Expected: result equals `7.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (float - int)")
val result = 10.5 - 3
expect(result).to_equal(7.5)
```

</details>

### Arithmetic Operators - Multiplication

#### with integers

#### multiplies positive integers

- multiplies positive integers
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies positive integers")
val result = 4 * 5
expect(result).to_equal(20)
```

</details>

#### multiplies by zero

- multiplies by zero
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by zero")
val result = 42 * 0
expect(result).to_equal(0)
```

</details>

#### multiplies by one

- multiplies by one
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by one")
val result = 42 * 1
expect(result).to_equal(42)
```

</details>

#### multiplies negative numbers

- multiplies negative numbers
   - Expected: result equals `-12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies negative numbers")
val result = -3 * 4
expect(result).to_equal(-12)
```

</details>

#### multiplies two negatives

- multiplies two negatives
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies two negatives")
val result = -3 * -4
expect(result).to_equal(12)
```

</details>

#### with floats

#### multiplies positive floats

- multiplies positive floats
   - Expected: result equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies positive floats")
val result = 2.5 * 4.0
expect(result).to_equal(10.0)
```

</details>

#### with mixed types

#### promotes int to float (int * float)

- promotes int to float (int * float)
   - Expected: result equals `12.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (int * float)")
val result = 5 * 2.5
expect(result).to_equal(12.5)
```

</details>

#### promotes int to float (float * int)

- promotes int to float (float * int)
   - Expected: result equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (float * int)")
val result = 3.5 * 2
expect(result).to_equal(7.0)
```

</details>

### Arithmetic Operators - Division

#### with integers

#### divides evenly

- divides evenly
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides evenly")
val result = 20 / 4
expect(result).to_equal(5)
```

</details>

#### divides with remainder

- divides with remainder
   - Expected: result equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides with remainder")
val result = 17 / 5
expect(result).to_equal(3)
```

</details>

#### divides one by itself

- divides one by itself
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides one by itself")
val result = 42 / 42
expect(result).to_equal(1)
```

</details>

#### with floats

#### divides floats

- divides floats
   - Expected: result equals `2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides floats")
val result = 10.0 / 4.0
expect(result).to_equal(2.5)
```

</details>

#### with mixed types

#### promotes int to float (int / float)

- promotes int to float (int / float)
   - Expected: result equals `2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (int / float)")
val result = 10 / 4.0
expect(result).to_equal(2.5)
```

</details>

#### promotes int to float (float / int)

- promotes int to float (float / int)
   - Expected: result equals `2.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes int to float (float / int)")
val result = 10.0 / 4
expect(result).to_equal(2.5)
```

</details>

### Arithmetic Operators - Modulo

#### with positive integers

#### computes remainder

- computes remainder
   - Expected: result equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes remainder")
val result = 17 % 5
expect(result).to_equal(2)
```

</details>

#### returns zero for even division

- returns zero for even division
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns zero for even division")
val result = 20 % 4
expect(result).to_equal(0)
```

</details>

#### returns operand when divisor is larger

- returns operand when divisor is larger
   - Expected: result equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns operand when divisor is larger")
val result = 3 % 5
expect(result).to_equal(3)
```

</details>

#### with negative integers

#### handles negative dividend

- handles negative dividend
   - Expected: result equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles negative dividend")
val result = -17 % 5
expect(result).to_equal(-2)
```

</details>

#### handles negative divisor

- handles negative divisor
   - Expected: result equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles negative divisor")
val result = 17 % -5
expect(result).to_equal(2)
```

</details>

### Arithmetic Operators - Exponentiation

#### with integers

#### computes square

- computes square
   - Expected: result equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes square")
val result = 5 ** 2
expect(result).to_equal(25)
```

</details>

#### computes cube

- computes cube
   - Expected: result equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes cube")
val result = 2 ** 3
expect(result).to_equal(8)
```

</details>

#### computes power of zero

- computes power of zero
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes power of zero")
val result = 42 ** 0
expect(result).to_equal(1)
```

</details>

#### computes power of one

- computes power of one
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes power of one")
val result = 42 ** 1
expect(result).to_equal(42)
```

</details>

#### with floats

#### computes float power

- computes float power
   - Expected: result equals `8.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes float power")
val result = 2.0 ** 3.0
expect(result).to_equal(8.0)
```

</details>

#### with right associativity

#### evaluates right to left

- evaluates right to left
   - Expected: result equals `512`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates right to left")
val result = 2 ** 3 ** 2
expect(result).to_equal(512)
```

</details>

### Arithmetic Operators - Floor Division

#### with positive integers

#### divides and floors

- divides and floors
   - Expected: result equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides and floors")
val result = 17.fdiv(5)
expect(result).to_equal(3)
```

</details>

#### returns exact result for even division

- returns exact result for even division
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns exact result for even division")
val result = 20.fdiv(4)
expect(result).to_equal(5)
```

</details>

### Arithmetic Operators - Unary Negation

#### with integers

#### negates positive integer

- negates positive integer
   - Expected: result equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates positive integer")
val result = -42
expect(result).to_equal(-42)
```

</details>

#### negates negative integer

- negates negative integer
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates negative integer")
val x = -42
val result = -x
expect(result).to_equal(42)
```

</details>

#### negates zero

- negates zero
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates zero")
val result = -0
expect(result).to_equal(0)
```

</details>

#### with floats

#### negates positive float

- negates positive float
   - Expected: result equals `-3.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates positive float")
val result = -3.5
expect(result).to_equal(-3.5)
```

</details>

#### with expressions

#### negates expression result

- negates expression result
   - Expected: result equals `-8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negates expression result")
val result = -(5 + 3)
expect(result).to_equal(-8)
```

</details>

### Arithmetic Operators - Precedence

#### multiplication before addition

#### evaluates multiplication first

- evaluates multiplication first
   - Expected: result equals `14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates multiplication first")
val result = 2 + 3 * 4
expect(result).to_equal(14)
```

</details>

#### uses parentheses to override

- uses parentheses to override
   - Expected: result equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses parentheses to override")
val result = (2 + 3) * 4
expect(result).to_equal(20)
```

</details>

#### exponentiation before multiplication

#### evaluates exponentiation first

- evaluates exponentiation first
   - Expected: result equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates exponentiation first")
val result = 2 * 3 ** 2
expect(result).to_equal(18)
```

</details>

#### uses parentheses to override

- uses parentheses to override
   - Expected: result equals `36`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses parentheses to override")
val result = (2 * 3) ** 2
expect(result).to_equal(36)
```

</details>

#### complex expressions

#### evaluates complex expression correctly

- evaluates complex expression correctly
   - Expected: result equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates complex expression correctly")
val result = 2 + 3 * 4 - 5
expect(result).to_equal(9)
```

</details>

#### evaluates with division

- evaluates with division
   - Expected: result equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates with division")
val result = 20 / 4 + 3 * 2
expect(result).to_equal(11)
```

</details>

### Arithmetic Operators - Type Coercion

#### in complex expressions

#### promotes in nested expressions

- promotes in nested expressions
   - Expected: result equals `20.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes in nested expressions")
val result = 10 + 5 * 2.0
expect(result).to_equal(20.0)
```

</details>

#### promotes across multiple operations

- promotes across multiple operations
   - Expected: result equals `6.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("promotes across multiple operations")
val result = 1 + 2 + 3.0
expect(result).to_equal(6.0)
```

</details>

### Arithmetic Operators - Edge Cases

#### with zero

#### multiplies by zero

- multiplies by zero
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by zero")
val result = 42 * 0
expect(result).to_equal(0)
```

</details>

#### adds zero (identity)

- adds zero (identity)
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("adds zero (identity)")
val result = 42 + 0
expect(result).to_equal(42)
```

</details>

#### with one

#### multiplies by one

- multiplies by one
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiplies by one")
val result = 42 * 1
expect(result).to_equal(42)
```

</details>

#### divides by one

- divides by one
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("divides by one")
val result = 42 / 1
expect(result).to_equal(42)
```

</details>

#### raises to power of zero

- raises to power of zero
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("raises to power of zero")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `26eb7055ac05f01ddbefba78bb7b073c18b1fe7d488872070ee11f7a51cfc985`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `26eb7055ac05f01ddbefba78bb7b073c18b1fe7d488872070ee11f7a51cfc985`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `26eb7055ac05f01ddbefba78bb7b073c18b1fe7d488872070ee11f7a51cfc985`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/operators_arithmetic_spec.spl
mirror: doc/06_spec/feature/usage/operators_arithmetic_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/operators_arithmetic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/operators_arithmetic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/operators_arithmetic_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 59 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/operators_arithmetic_spec.spl:137:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds positive integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/operators_arithmetic_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds negative integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/operators_arithmetic_spec.spl:149:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
