# LLVM Backend Differential Testing

> Tests differential correctness between the LLVM backend and other compilation backends. Verifies that LLVM-generated code produces identical results to the reference backend across a suite of test programs and edge cases.

<!-- sdn-diagram:id=differential_llvm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=differential_llvm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

differential_llvm_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=differential_llvm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LLVM Backend Differential Testing

Tests differential correctness between the LLVM backend and other compilation backends. Verifies that LLVM-generated code produces identical results to the reference backend across a suite of test programs and edge cases.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/backend/differential_llvm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests differential correctness between the LLVM backend and other compilation
backends. Verifies that LLVM-generated code produces identical results to the
reference backend across a suite of test programs and edge cases.

## Scenarios

### Differential Testing - Arithmetic

#### integer addition

#### computes 2 + 3 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 2
val b = 3
val result = a + b
expect(result).to_equal(5)
```

</details>

#### computes large numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1000000
val b = 2000000
val result = a + b
expect(result).to_equal(3000000)
```

</details>

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = -5
val b = 3
val result = a + b
expect(result).to_equal(-2)
```

</details>

#### integer subtraction

#### computes 10 - 4 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 4
val result = a - b
expect(result).to_equal(6)
```

</details>

#### handles negative results

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 3
val b = 7
val result = a - b
expect(result).to_equal(-4)
```

</details>

#### integer multiplication

#### computes 6 * 7 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 6
val b = 7
val result = a * b
expect(result).to_equal(42)
```

</details>

#### handles zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 100
val b = 0
val result = a * b
expect(result).to_equal(0)
```

</details>

#### integer division

#### computes 20 / 4 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 20
val b = 4
val result = a / b
expect(result).to_equal(5)
```

</details>

#### truncates toward zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 7
val b = 2
val result = a / b
expect(result).to_equal(3)
```

</details>

#### modulo operation

#### computes 10 % 3 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 3
val result = a % b
expect(result).to_equal(1)
```

</details>

#### negation

#### negates positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 42
val result = -a
expect(result).to_equal(-42)
```

</details>

#### negates negative number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = -17
val result = -a
expect(result).to_equal(17)
```

</details>

### Differential Testing - Bitwise

#### bitwise AND

#### computes 12 & 10 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 12  # 1100
val b = 10  # 1010
val result = a & b  # 1000 = 8
expect(result).to_equal(8)
```

</details>

#### bitwise OR

#### computes 12 | 10 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 12  # 1100
val b = 10  # 1010
val result = a | b  # 1110 = 14
expect(result).to_equal(14)
```

</details>

#### bitwise XOR

#### computes 12 xor 10 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 12  # 1100
val b = 10  # 1010
val result = a xor b  # 0110 = 6
expect(result).to_equal(6)
```

</details>

#### left shift

#### computes 5 << 2 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5  # 101
val result = a << 2  # 10100 = 20
expect(result).to_equal(20)
```

</details>

#### right shift

#### computes 20 >> 2 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 20  # 10100
val result = a >> 2  # 101 = 5
expect(result).to_equal(5)
```

</details>

#### bitwise NOT

#### computes ~0 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 0
val result = ~a
expect(result).to_equal(-1)
```

</details>

### Differential Testing - Comparisons

#### equality

#### compares equal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 42
val b = 42
val result = a == b
expect(result).to_equal(true)
```

</details>

#### compares unequal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val result = a == b
expect(result).to_equal(false)
```

</details>

#### inequality

#### compares different numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
val result = a != b
expect(result).to_equal(true)
```

</details>

#### less than

#### compares smaller to larger

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
val result = a < b
expect(result).to_equal(true)
```

</details>

#### compares larger to smaller

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 5
val result = a < b
expect(result).to_equal(false)
```

</details>

#### less than or equal

#### compares equal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 10
val result = a <= b
expect(result).to_equal(true)
```

</details>

#### compares smaller to larger

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
val result = a <= b
expect(result).to_equal(true)
```

</details>

#### greater than

#### compares larger to smaller

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 15
val b = 10
val result = a > b
expect(result).to_equal(true)
```

</details>

#### greater than or equal

#### compares equal numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 10
val result = a >= b
expect(result).to_equal(true)
```

</details>

### Differential Testing - Control Flow

#### if statements

#### executes then branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
if 5 > 3:
    result = 1
else:
    result = 2
expect(result).to_equal(1)
```

</details>

#### executes else branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
if 3 > 5:
    result = 1
else:
    result = 2
expect(result).to_equal(2)
```

</details>

#### loops

<details>
<summary>Advanced: executes for loop</summary>

#### executes for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    sum = sum + i
expect(sum).to_equal(10)  # 0+1+2+3+4 = 10
```

</details>


</details>

<details>
<summary>Advanced: executes while loop</summary>

#### executes while loop

1. fn run while
   - Expected: run_while() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_while() -> i64:
    var count = 0
    var i = 0
    while i < 5:
        count = count + 1
        i = i + 1
    count
expect(run_while()).to_equal(5)
```

</details>


</details>

### Differential Testing - Functions

#### simple functions

#### calls function with no parameters

1. fn get value
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    42
val result = get_value()
expect(result).to_equal(42)
```

</details>

#### calls function with parameters

1. fn add
   - Expected: result equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b
val result = add(10, 20)
expect(result).to_equal(30)
```

</details>

#### calls function multiple times

1. fn square
   - Expected: r1 equals `9`
   - Expected: r2 equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x: i64) -> i64:
    x * x
val r1 = square(3)
val r2 = square(4)
expect(r1).to_equal(9)
expect(r2).to_equal(16)
```

</details>

#### recursive functions

#### computes factorial

1. fn factorial
2. n * factorial
   - Expected: result equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn factorial(n: i64) -> i64:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)
val result = factorial(5)
expect(result).to_equal(120)
```

</details>

### Differential Testing - Variables

#### immutable variables

#### reads immutable variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = x + 5
expect(y).to_equal(15)
```

</details>

#### mutable variables

#### updates mutable variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 10
x = x + 5
expect(x).to_equal(15)
```

</details>

#### updates multiple times

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 1
x = x + 1
x = x + 1
x = x + 1
expect(x).to_equal(4)
```

</details>

### Differential Testing - Boolean Logic

#### logical AND

#### computes true && true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = true and true
expect(result).to_equal(true)
```

</details>

#### computes true && false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = true and false
expect(result).to_equal(false)
```

</details>

#### logical OR

#### computes false || true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = false or true
expect(result).to_equal(true)
```

</details>

#### computes false || false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = false or false
expect(result).to_equal(false)
```

</details>

#### logical NOT

#### computes !true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = not true
expect(result).to_equal(false)
```

</details>

#### computes !false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = not false
expect(result).to_equal(true)
```

</details>

### Differential Testing - Complex Expressions

#### nested arithmetic

#### evaluates (2 + 3) * (4 + 5)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (2 + 3) * (4 + 5)
expect(result).to_equal(45)
```

</details>

#### respects operator precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3 * 4
expect(result).to_equal(14)
```

</details>

#### mixed operations

#### combines arithmetic and bitwise

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (5 + 3) & 7
expect(result).to_equal(0)
```

</details>

#### combines comparisons and logic

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (5 > 3) and (10 < 20)
expect(result).to_equal(true)
```

</details>

### Differential Testing - Edge Cases

#### zero values

#### handles zero in addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0 + 0
expect(result).to_equal(0)
```

</details>

#### handles zero in multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 100 * 0
expect(result).to_equal(0)
```

</details>

#### boundary values

#### handles small positive number

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 + 1
expect(result).to_equal(2)
```

</details>

#### handles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -10 + 5
expect(result).to_equal(-5)
```

</details>

### Differential Testing - Type Conversions

#### integer types

#### works with i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 100
val result = x + 50
expect(result).to_equal(150)
```

</details>

### Differential Testing - Aggregates

#### tuples

#### creates and accesses tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = (10, 20)
val a = pair.0
val b = pair.1
expect(a).to_equal(10)
expect(b).to_equal(20)
```

</details>

### Differential Testing - Strings

#### string operations

#### works with string literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.len()).to_equal(5)
```

</details>

### Differential Testing - Summary

#### comprehensive smoke test

#### runs comprehensive computation

1. result = result +
   - Expected: result equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test combines multiple operations
var result = 0

# Arithmetic
result = result + (10 + 5)  # 15
result = result * 2          # 30

# Bitwise
result = result | 1          # 31

# Comparison and branching
if result > 20:
    result = result - 1      # 30

# Loop
for i in 0..3:
    result = result + 1      # 33

expect(result).to_equal(33)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
