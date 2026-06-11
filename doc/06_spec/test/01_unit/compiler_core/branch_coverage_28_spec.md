# Branch Coverage Test Suite - Error Paths & Edge Cases

> Tests error handling and edge case branches to achieve 100% coverage. Covers boundary conditions, error recovery, and uncommon code paths.

<!-- sdn-diagram:id=branch_coverage_28_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_28_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_28_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_28_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 67 | 67 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Error Paths & Edge Cases

Tests error handling and edge case branches to achieve 100% coverage. Covers boundary conditions, error recovery, and uncommon code paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #ERROR #EDGE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_28_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests error handling and edge case branches to achieve 100% coverage.
Covers boundary conditions, error recovery, and uncommon code paths.

## Scenarios

### Boundary Conditions

#### integer - zero

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0 == 0)
check(0 < 1)
check(0 > -1)
```

</details>

#### integer - min value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -9223372036854775808
check(x < 0)
```

</details>

#### integer - max value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 9223372036854775807
check(x > 0)
```

</details>

#### float - zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0.0
check(x == 0.0)
```

</details>

#### float - negative zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -0.0
check(x == 0.0)
```

</details>

#### float - infinity

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0e308
check(x > 0.0)
```

</details>

#### float - tiny

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1.0e-308
check(x > 0.0)
check(x < 1.0)
```

</details>

#### string - empty

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
check(s.len() == 0)
check(s == "")
```

</details>

#### string - single char

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "a"
check(s.len() == 1)
```

</details>

#### string - very long

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
check(s.len() > 60)
```

</details>

#### array - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
check(arr.len() == 0)
```

</details>

#### array - single element

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [42]
check(arr.len() == 1)
```

</details>

#### array - large

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20]
check(arr.len() == 20)
```

</details>

### Edge Case Expressions

#### division by one

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 / 1 == 10)
```

</details>

#### modulo by one

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 % 1 == 0)
```

</details>

#### power of zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 ** 0 == 1)
```

</details>

#### power of one

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 ** 1 == 5)
```

</details>

#### negative exponent handled

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2 ** 3
check(x == 8)
```

</details>

#### zero to power

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0 ** 5 == 0)
```

</details>

#### one to power

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 ** 100 == 1)
```

</details>

#### bitwise - all zeros

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((0 & 0) == 0)
check((0 | 0) == 0)
check((0 ^ 0) == 0)
```

</details>

#### bitwise - all ones

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((15 & 15) == 15)
check((15 | 15) == 15)
check((15 ^ 15) == 0)
```

</details>

#### bitwise - mixed

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((0b1010 & 0b1100) == 0b1000)
check((0b1010 | 0b1100) == 0b1110)
check((0b1010 ^ 0b1100) == 0b0110)
```

</details>

### Complex Control Flow

<details>
<summary>Advanced: nested loops - break outer effect</summary>

#### nested loops - break outer effect

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..3:
    for j in 0..3:
        count = count + 1
        if count == 5:
            break
check(count >= 5)
```

</details>


</details>

<details>
<summary>Advanced: nested loops - continue inner</summary>

#### nested loops - continue inner

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..3:
        for j in 0..3:
            if j == 1:
                continue
            count = count + 1
    count
check(run() == 6)
```

</details>


</details>

#### nested if-elif-else

1. fn classify
2. check
3. check
4. check
5. check
6. check
7. check
8. check
9. check
10. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64, y: i64) -> i64:
    if x > 0:
        if y > 0:
            return 1
        elif y == 0:
            return 2
        else:
            return 3
    elif x == 0:
        if y > 0:
            return 4
        elif y == 0:
            return 5
        else:
            return 6
    else:
        if y > 0:
            return 7
        elif y == 0:
            return 8
        else:
            return 9
check(classify(1, 1) == 1)
check(classify(1, 0) == 2)
check(classify(1, -1) == 3)
check(classify(0, 1) == 4)
check(classify(0, 0) == 5)
check(classify(0, -1) == 6)
check(classify(-1, 1) == 7)
check(classify(-1, 0) == 8)
check(classify(-1, -1) == 9)
```

</details>

<details>
<summary>Advanced: match in loop</summary>

#### match in loop

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    val add = match i:
        0: 1
        1: 2
        2: 3
        3: 4
        _: 5
    sum = sum + add
check(sum == 15)
```

</details>


</details>

#### if in match

1. fn test
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64) -> i64:
    match x:
        1:
            if true:
                10
            else:
                20
        2:
            if false:
                30
            else:
                40
        _:
            50
check(test(1) == 10)
check(test(2) == 40)
check(test(3) == 50)
```

</details>

### Short Circuit Evaluation

#### and - short circuit false

1. fn side effect
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn side_effect() -> bool:
    true
val result = false and side_effect()
check(not result)
```

</details>

#### and - no short circuit true

1. fn side effect2
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn side_effect2() -> bool:
    true
val result = true and side_effect2()
check(result)
```

</details>

#### or - short circuit true

1. fn side effect3
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn side_effect3() -> bool:
    false
val result = true or side_effect3()
check(result)
```

</details>

#### or - no short circuit false

1. fn side effect4
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn side_effect4() -> bool:
    true
val result = false or side_effect4()
check(result)
```

</details>

### String Operations All Branches

#### concat - empty + empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "" + ""
check(s == "")
```

</details>

#### concat - empty + non-empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "" + "hello"
check(s == "hello")
```

</details>

#### concat - non-empty + empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello" + ""
check(s == "hello")
```

</details>

#### concat - non-empty + non-empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello" + " world"
check(s == "hello world")
```

</details>

#### string contains - empty in empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("".contains(""))
```

</details>

#### string contains - empty in non-empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("hello".contains(""))
```

</details>

#### string contains - found

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("hello".contains("ell"))
```

</details>

#### string contains - not found

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not "hello".contains("xyz"))
```

</details>

#### string starts_with - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("hello".starts_with(""))
```

</details>

#### string starts_with - match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("hello".starts_with("hel"))
```

</details>

#### string starts_with - no match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not "hello".starts_with("llo"))
```

</details>

#### string ends_with - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("hello".ends_with(""))
```

</details>

#### string ends_with - match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("hello".ends_with("llo"))
```

</details>

#### string ends_with - no match

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not "hello".ends_with("hel"))
```

</details>

### Array Operations All Branches

#### array push

1. arr push
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2]
arr.push(3)
check(arr.len() == 3)
```

</details>

#### array pop - non-empty

1. fn run
2. arr len
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var arr = [1, 2, 3]
    val x = arr.pop()
    arr.len()
check(run() == 2)
```

</details>

#### array pop - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr: [i64] = []
val x = arr.pop()
check(not x.?)
```

</details>

#### array contains - found

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
check(arr.contains(2))
```

</details>

#### array contains - not found

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
check(not arr.contains(5))
```

</details>

#### array contains - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr: [i64] = []
check(not arr.contains(1))
```

</details>

### Range All Branches

#### range - positive

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..5:
    count = count + 1
check(count == 5)
```

</details>

#### range - zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..0:
    count = count + 1
check(count == 0)
```

</details>

#### range - single

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 5..6:
    count = count + 1
check(count == 1)
```

</details>

#### range - negative start

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in -2..2:
    count = count + 1
check(count == 4)
```

</details>

### Type Coercion All Branches

#### int to float implicit

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: f64 = 5.0 + 3.0
check(x == 8.0)
```

</details>

#### bool to int context

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = if true: 1 else: 0
val f = if false: 1 else: 0
check(t == 1)
check(f == 0)
```

</details>

### Variable Scope All Branches

#### block scope - inner shadows outer

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
var result = 0
if true:
    val x = 20
    result = x
check(result == 20)
```

</details>

#### block scope - outer visible after

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
if true:
    val y = 20
check(x == 10)
```

</details>

<details>
<summary>Advanced: loop scope - variable local</summary>

#### loop scope - variable local

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..3:
    val temp = i * 2
    sum = sum + temp
check(sum == 6)
```

</details>


</details>

### Comparison All Branches

#### compare - equal same type

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 == 5)
check("hello" == "hello")
check(true == true)
```

</details>

#### compare - not equal same type

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 != 4)
check("hello" != "world")
check(true != false)
```

</details>

#### compare - less than

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(3 < 5)
check(not (5 < 3))
check(not (5 < 5))
```

</details>

#### compare - greater than

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 > 3)
check(not (3 > 5))
check(not (5 > 5))
```

</details>

#### compare - less or equal

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(3 <= 5)
check(5 <= 5)
check(not (5 <= 3))
```

</details>

#### compare - greater or equal

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 >= 3)
check(5 >= 5)
check(not (3 >= 5))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 67 |
| Active scenarios | 67 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
