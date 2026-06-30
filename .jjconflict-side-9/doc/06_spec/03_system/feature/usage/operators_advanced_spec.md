# Advanced Operators Specification

> let x = 10       # immutable

<!-- sdn-diagram:id=operators_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=operators_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

operators_advanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=operators_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 52 | 52 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Operators Specification

let x = 10       # immutable

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OP-ADV-001 to #OP-ADV-030 |
| Category | Language \| Operators |
| Status | Implemented |
| Source | `test/03_system/feature/usage/operators_advanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Mutability
let x = 10       # immutable
let mut y = 10   # mutable with let mut
var z = 10       # mutable with var
const MAX = 100  # constant
static counter = 0  # static variable

# Operators
val a = 12 & 10    # bitwise AND
val b = 2 ** 10    # power
val c = 7.fdiv(2)  # floor division (// is now parallel operator)
val d = "ell" in "hello"  # in operator
```

## Scenarios

### Mutability Control

#### let is immutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
# x = 20  # Would be error
expect x == 10
```

</details>

#### var is mutable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var y = 10
y = 30
expect y == 30
```

</details>

<details>
<summary>Advanced: var in loop</summary>

#### var in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
var i = 0
while i < 5:
    sum = sum + i
    i = i + 1
expect sum == 10  # 0+1+2+3+4
```

</details>


</details>

#### const declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
const MAX = 100
expect MAX == 100
```

</details>

#### const with arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
const BASE = 10
const MULTIPLIER = 5
expect BASE * MULTIPLIER == 50
```

</details>

#### const with type annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
const SIZE: i64 = 256
expect SIZE == 256
```

</details>

#### static variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
static counter = 42
expect counter == 42
```

</details>

### Lambda Expressions

#### basic lambda

1. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val double = \x: x * 2
expect double(21) == 42
```

</details>

#### lambda with multiple params

1. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val add = \a, b: a + b
expect add(10, 32) == 42
```

</details>

#### lambda as higher-order

1. fn apply
2. f
3. expect apply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn apply(f, x):
    f(x)

val inc = \n: n + 1
expect apply(inc, 41) == 42
```

</details>

### String Operations

#### string length

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect s.len() == 5
```

</details>

#### string concatenation

1. expect c len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "hello"
val b = "world"
val c = a + " " + b
expect c.len() == 11
```

</details>

#### string interpolation

1. expect s len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val s = "value is {x}"
expect s.len() == 11
```

</details>

### Array Methods

#### array length

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect arr.len() == 5
```

</details>

### Dict Methods

#### dict length

1. expect d len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 1, "b": 2, "c": 3}
expect d.len() == 3
```

</details>

#### dict keys

1. expect keys len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"x": 10, "y": 20}
val keys = d.keys()
expect keys.len() == 2
```

</details>

#### dict values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 5, "b": 10}
val vals = d.values()
expect vals[0] + vals[1] == 15
```

</details>

#### dict contains_key

1. expect d has


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"hello": 1}
expect d.has("hello")
```

</details>

### Bitwise Operators

#### bitwise AND

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (12 & 10) == 8  # 1100 & 1010 = 1000
```

</details>

#### bitwise OR

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (12 | 10) == 14  # 1100 | 1010 = 1110
```

</details>

#### bitwise XOR

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (12 xor 10) == 6  # 1100 ^ 1010 = 0110
```

</details>

#### left shift

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (1 << 4) == 16
```

</details>

#### right shift

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (16 >> 2) == 4
```

</details>

#### bitwise NOT

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (~0) == -1
```

</details>

### Comparison Operators

#### less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 < 2
```

</details>

#### greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 > 1
```

</details>

#### less than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 <= 2
```

</details>

#### greater than or equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 >= 2
```

</details>

#### equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 == 2
```

</details>

#### not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 != 3
```

</details>

### Logical Operators

#### and operator

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true and true
expect not (true and false)
```

</details>

#### or operator

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect true or false
expect not (false or false)
```

</details>

#### not operator

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not false
expect not (not true)
```

</details>

### Power Operator

#### power of zero

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 ** 0) == 1
```

</details>

#### power of one

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 ** 1) == 2
```

</details>

#### power of three

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 ** 3) == 8
```

</details>

#### power of ten

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (2 ** 10) == 1024
```

</details>

#### three to fourth

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (3 ** 4) == 81
```

</details>

### Floor Division

#### positive floor division

1. expect 7 fdiv


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 7.fdiv(2) == 3
```

</details>

#### another floor division

1. expect 10 fdiv


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 10.fdiv(3) == 3
```

</details>

#### negative floor division

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (-7).fdiv(2) == -4  # rounds toward negative infinity
```

</details>

#### exact division

1. expect 8 fdiv


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 8.fdiv(4) == 2
```

</details>

### In Operator

#### in array present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 2 in [1, 2, 3]
```

</details>

#### in array absent

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not (5 in [1, 2, 3])
```

</details>

#### in string present

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect "ell" in "hello"
```

</details>

#### in string absent

1. expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect not ("xyz" in "hello")
```

</details>

### Recursive Functions

#### factorial

1. fn factorial
2. n * factorial
3. expect factorial


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

expect factorial(3) == 6
```

</details>

### Nested Data Structures

#### nested arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [[1, 2], [3, 4], [5, 6]]
expect arr[0][0] + arr[1][1] + arr[2][0] == 10
```

</details>

#### nested structs

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Inner:
    value: i64

struct Outer:
    inner: Inner

val o = Outer(inner: Inner(value: 42))
expect o.inner.value == 42
```

</details>

### Early Return

#### early return based on condition

1. fn verify
2. expect verify


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn verify(x: i64) -> i64:
    if x > 10:
        return 1
    if x > 5:
        return 2
    3

expect verify(7) == 2
```

</details>

### Tuple Destructuring

#### destructures tuple

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val _tuple = (1, 2, 3)
val a = _tuple[0]
val b = _tuple[1]
val c = _tuple[2]
expect a + b + c == 6
```

</details>

### Symbols

#### symbol comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = :hello
expect s == :hello
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 52 |
| Active scenarios | 52 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
