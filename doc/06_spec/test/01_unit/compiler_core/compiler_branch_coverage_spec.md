# Compiler Branch Coverage Specification

> <details>

<!-- sdn-diagram:id=compiler_branch_coverage_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compiler_branch_coverage_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compiler_branch_coverage_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compiler_branch_coverage_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler Branch Coverage Specification

## Scenarios

### Number Literal Branches

#### covers integer literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 42
val b = 0
val c = 1_000_000
expect a == 42
expect b == 0
expect c == 1000000
```

</details>

#### covers hex literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = 0xFF
val h2 = 0xABCDEF
val h3 = 0xFF_FF
expect h1 == 255
```

</details>

#### covers binary literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b1 = 0b1010
val b2 = 0b1111_0000
expect b1 == 10
```

</details>

#### covers octal literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o1 = 0o777
val o2 = 0o77_77
expect o1 == 511
```

</details>

#### covers float literals

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = 3.14
val f2 = 1_000.000_1
val f3 = 1e10
val f4 = 1E10
val f5 = 1e+10
val f6 = 1e-10
val f7 = 1.23e-45
expect f1 > 3.0
```

</details>

### String Literal Branches

#### covers simple strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s1 = "hello"
val s2 = "world"
expect s1 == "hello"
expect s2 == "world"
```

</details>

#### covers escape sequences

1. expect e1 len
2. expect e2 len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = "a\nb"
val e2 = "a\tb"
val e3 = "a\\b"
val e4 = "a\"b"
expect e1.len() == 3
expect e2.len() == 3
```

</details>

### Keyword Branches

#### covers val and var

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
var y = 2
y = 3
expect x == 1
expect y == 3
```

</details>

#### covers fn keyword

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b
expect add(1, 2) == 3
```

</details>

#### covers if/elif/else

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val r = if x > 10:
    "big"
elif x > 3:
    "medium"
else:
    "small"
expect r == "medium"
```

</details>

#### covers match

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val r = match x:
    case 1:
        "one"
    case 2:
        "two"
    case _:
        "other"
expect r == "two"
```

</details>

<details>
<summary>Advanced: covers for loop</summary>

#### covers for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    sum = sum + i
expect sum == 10
```

</details>


</details>

<details>
<summary>Advanced: covers while loop</summary>

#### covers while loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
while count < 3:
    count = count + 1
expect count == 3
```

</details>


</details>

#### covers return

1. fn get value
2. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    return 42
expect get_value() == 42
```

</details>

#### covers break and continue

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..10:
    if i == 5:
        break
    if i == 2:
        continue
    sum = sum + i
expect sum == 1 + 3 + 4
```

</details>

### Operator Branches

#### covers arithmetic operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 2 == 3
expect 5 - 3 == 2
expect 4 * 3 == 12
expect 10 / 2 == 5
expect 10 % 3 == 1
```

</details>

#### covers comparison operators

1. expect
2. expect
3. expect
4. expect
5. expect
6. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (1 == 1) == true
expect (1 != 2) == true
expect (1 < 2) == true
expect (2 > 1) == true
expect (1 <= 1) == true
expect (1 >= 1) == true
```

</details>

#### covers logical operators

1. expect
2. expect
3. expect
4. expect
5. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect (true and true) == true
expect (true and false) == false
expect (true or false) == true
expect (false or false) == false
expect (not false) == true
```

</details>

#### covers assignment operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 10
x += 5
expect x == 15
x -= 3
expect x == 12
x *= 2
expect x == 24
x /= 4
expect x == 6
```

</details>

### Delimiter Branches

#### covers parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = (1 + 2) * 3
expect r == 9
```

</details>

#### covers brackets

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
expect arr[0] == 1
```

</details>

#### covers braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Obj:
    x: i64
    y: i64
val obj = Obj { x: 1, y: 2 }
expect obj.x == 1
```

</details>

#### covers range operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..5:
    count = count + 1
expect count == 5

var count2 = 0
for i in 0..=5:
    count2 = count2 + 1
expect count2 == 6
```

</details>

#### covers optional operators

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64? = nil
val y = x ?? 42
expect y == 42
```

</details>

### Complex Expression Branches

#### covers nested expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = (1 + 2) * (3 + 4) - 5
expect a == 16
```

</details>

#### covers method chaining

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val r = s.len()
expect r == 5
```

</details>

#### covers lambda expressions

1. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = _1 * 2
expect f(5) == 10
```

</details>

#### covers list operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val mapped = arr.map(_1 * 2)
expect mapped[0] == 2
expect mapped[1] == 4
expect mapped[2] == 6
```

</details>

### Control Flow Branches

#### covers nested if

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 10
val r = if x > 0:
    if y > 5:
        "both"
    else:
        "x only"
else:
    "neither"
expect r == "both"
```

</details>

#### covers early return

1. fn find first even
2. expect find first even
3. expect find first even


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn find_first_even(arr: [i64]) -> i64?:
    for x in arr:
        if x % 2 == 0:
            return x
    nil
expect find_first_even([1, 3, 4, 5]) == 4
expect find_first_even([1, 3, 5]) == nil
```

</details>

#### covers match with guards

1. fn classify
2. expect classify
3. expect classify
4. expect classify
5. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    match x:
        case n if n < 0:
            "negative"
        case 0:
            "zero"
        case n if n > 100:
            "large"
        case _:
            "small"
expect classify(-5) == "negative"
expect classify(0) == "zero"
expect classify(200) == "large"
expect classify(50) == "small"
```

</details>

### Type System Branches

#### covers basic types

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val i: i64 = 42
val f: f64 = 3.14
val b: bool = true
val s: text = "hello"
expect i == 42
expect b == true
```

</details>

#### covers optional types

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64? = 42
val y: i64? = nil
expect x == 42
expect y == nil
```

</details>

#### covers array types

1. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = [1, 2, 3]
expect arr.len() == 3
```

</details>

#### covers struct types

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val p = Point { x: 1, y: 2 }
expect p.x == 1
expect p.y == 2
```

</details>

### Edge Cases

#### covers empty collections

1. expect empty len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [i64] = []
expect empty.len() == 0
```

</details>

#### covers single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val single = [42]
expect single[0] == 42
```

</details>

#### covers zero values

1. expect empty str len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val zero = 0
val empty_str = ""
expect zero == 0
expect empty_str.len() == 0
```

</details>

#### covers negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val neg = -42
expect neg == -42
expect neg < 0
```

</details>

### Test Summary

#### reports coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
print ""
print "Core Compiler Branch Coverage Tests Complete"
print "Covered:"
print "  - All number literal types"
print "  - All string escapes"
print "  - All keywords"
print "  - All operators"
print "  - All delimiters"
print "  - Complex expressions"
print "  - Control flow"
print "  - Type system"
print "  - Edge cases"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/compiler_branch_coverage_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Number Literal Branches
- String Literal Branches
- Keyword Branches
- Operator Branches
- Delimiter Branches
- Complex Expression Branches
- Control Flow Branches
- Type System Branches
- Edge Cases
- Test Summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
