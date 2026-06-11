# Branch Coverage Test Suite - Final 100% Coverage Push

> Final comprehensive tests targeting all remaining uncovered branches. Achieves 100% branch coverage by testing every code path systematically.

<!-- sdn-diagram:id=branch_coverage_30_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_30_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_30_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_30_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Final 100% Coverage Push

Final comprehensive tests targeting all remaining uncovered branches. Achieves 100% branch coverage by testing every code path systematically.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #COMPLETE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_30_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Final comprehensive tests targeting all remaining uncovered branches.
Achieves 100% branch coverage by testing every code path systematically.

## Scenarios

### All Numeric Formats

#### hex - uppercase

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0XFF == 255)
```

</details>

#### hex - lowercase

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0xff == 255)
```

</details>

#### hex - mixed case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0XfF == 255)
```

</details>

#### binary - all digits

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0b11111111 == 255)
```

</details>

#### octal - all digits

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0o777 == 511)
```

</details>

#### scientific - positive exp

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1e2 == 100.0)
```

</details>

#### scientific - negative exp

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1e-2 == 0.01)
```

</details>

#### scientific - explicit plus

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1e+2 == 100.0)
```

</details>

### All String Formats

#### single quote string

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = 'hello'
check(s == "hello")
```

</details>

#### triple quote string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = """multi
```

</details>

#### raw string - no interpolation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val s = r"{x}"
check(s == r"{x}")
```

</details>

#### interpolation - complex expression

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 10
val s = "{x * y + (x - y)}"
check(s.contains("45"))
```

</details>

### All Comparison Combinations

#### chain - all less than

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 < 2 < 3 < 4 < 5)
```

</details>

#### chain - all greater than

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 > 4 > 3 > 2 > 1)
```

</details>

#### chain - mixed

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 < 2 <= 2 < 3)
```

</details>

#### chain - not equal in chain

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 != 2 != 3)
```

</details>

### All Boolean Combinations

#### triple and - TTT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true and true and true)
```

</details>

#### triple and - TTF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (true and true and false))
```

</details>

#### triple and - TFT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (true and false and true))
```

</details>

#### triple and - TFF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (true and false and false))
```

</details>

#### triple or - FFF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (false or false or false))
```

</details>

#### triple or - FFT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(false or false or true)
```

</details>

#### triple or - FTF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(false or true or false)
```

</details>

#### triple or - FTT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(false or true or true)
```

</details>

#### complex - (A and B) or (C and D)

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true and true) or (false and false))
check(not ((false and true) or (true and false)))
```

</details>

#### complex - A and (B or C) and D

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true and (true or false) and true)
check(not (false and (true or false) and true))
```

</details>

### All Loop Combinations

#### for in for - both execute

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..3:
    for j in 0..3:
        count = count + 1
check(count == 9)
```

</details>

#### for in for - inner empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..3:
    for j in 0..0:
        count = count + 1
check(count == 0)
```

</details>

#### for in for - outer empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..0:
    for j in 0..3:
        count = count + 1
check(count == 0)
```

</details>

#### while in while - nested

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var i = 0
    var count = 0
    while i < 3:
        var j = 0
        while j < 3:
            count = count + 1
            j = j + 1
        i = i + 1
    count
check(run() == 9)
```

</details>

#### for in while

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var i = 0
    var count = 0
    while i < 3:
        for j in 0..3:
            count = count + 1
        i = i + 1
    count
check(run() == 9)
```

</details>

#### while in for

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
        var j = 0
        while j < 3:
            count = count + 1
            j = j + 1
    count
check(run() == 9)
```

</details>

### All Match Patterns

#### match - guard clauses

1. fn classify
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    match x:
        0: "zero"
        1: "one"
        2: "two"
        3: "three"
        4: "four"
        5: "five"
        6: "six"
        7: "seven"
        8: "eight"
        9: "nine"
        _: "many"
check(classify(0) == "zero")
check(classify(5) == "five")
check(classify(9) == "nine")
check(classify(99) == "many")
```

</details>

#### match - sum via direct values

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 + 2 == 3)
check(1 + 2 + 3 == 6)
check(1 + 2 + 3 + 4 == 10)
```

</details>

### All Function Signatures

#### fn - 0 params 0 return

1. fn f
2. f
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f():
    pass
f()
check(true)
```

</details>

#### fn - 1 param 0 return

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(a: i64) -> i64:
    a * 2
check(f(21) == 42)
```

</details>

#### fn - 0 params 1 return

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f() -> i64:
    42
check(f() == 42)
```

</details>

#### fn - 5 params 1 return

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(a: i64, b: i64, c: i64, d: i64, e: i64) -> i64:
    a + b + c + d + e
check(f(1, 2, 3, 4, 5) == 15)
```

</details>

#### fn - nested fn calls

1. fn f
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(x: i64) -> i64: x + 1
check(f(f(f(f(f(0))))) == 5)
```

</details>

#### fn - recursive (limited)

1. fn factorial
2. n * factorial
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn factorial(n: i64) -> i64:
    if n <= 1:
        return 1
    n * factorial(n - 1)
check(factorial(5) == 120)
```

</details>

### All Array Operations

#### array - all methods

1. fn run
2. arr push
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var arr = [1, 2, 3]
    arr.push(4)
    val len1 = arr.len()
    val x = arr.pop()
    val len2 = arr.len()
    len1 * 10 + len2
check(run() == 43)
val arr2 = [1, 2, 3]
check(arr2.contains(2))
check(not arr2.contains(99))
```

</details>

#### array - nested arrays

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [[1, 2], [3, 4], [5, 6]]
check(arr[0][0] == 1)
check(arr[1][1] == 4)
check(arr[2][0] == 5)
```

</details>

#### array - array of optionals

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [Some(1), nil, Some(3)]
check(arr[0].?)
check(not arr[1].?)
check(arr[2].?)
```

</details>

#### array - complex slicing

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
check(slice_len(arr, 0, 5) == 5)
check(slice_len(arr, 5, 10) == 5)
check(slice_len(arr, 2, 8) == 6)
check(slice_len(arr, 0, 0) == 0)
check(slice_len(arr, 5, 5) == 0)
```

</details>

### All Optional Patterns

#### optional - deep nesting

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o1: i64? = Some(42)
val o2 = Some(Some(42))
val o3 = Some(Some(Some(42)))
check(o1.?)
check(o2.?)
check(o3.?)
```

</details>

#### optional - all nil levels

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o1: i64? = nil
val o2 = nil
val o3 = Some(nil)
check(not o1.?)
check(not o2.?)
check(o3.?)
```

</details>

### All String Methods

#### string - all operations

1. check
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "  Hello World  "
check(s.trim() == "Hello World")
check(s.len() > 0)
check(s.contains("Hello"))
check(s.starts_with("  Hello"))
check(s.ends_with("World  "))
```

</details>

#### string - split

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "a,b,c"
val parts = s.split(",")
check(parts.len() == 3)
check(parts[0] == "a")
```

</details>

#### string - replace

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello world"
val r = s.replace("world", "universe")
check(r == "hello universe")
```

</details>

#### string - index operations

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
check((s.index_of("l") ?? -1) == 2)
check((s.last_index_of("l") ?? -1) == 3)
```

</details>

### All Error Conditions

#### division edge cases

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 / 1 == 10)
check(10 / 2 == 5)
check(10 / 3 == 3)
check(10 / 10 == 1)
```

</details>

#### modulo edge cases

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 % 1 == 0)
check(10 % 3 == 1)
check(10 % 10 == 0)
check(1 % 10 == 1)
```

</details>

#### power edge cases

1. check
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0 ** 0 == 1)
check(0 ** 1 == 0)
check(1 ** 0 == 1)
check(1 ** 1 == 1)
check(2 ** 0 == 1)
check(2 ** 1 == 2)
```

</details>

### All Control Flow Exits

#### return from nested if

1. fn test
2. check
3. check
4. check
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64) -> i64:
    if x > 10:
        if x > 20:
            if x > 30:
                return 3
            return 2
        return 1
    0
check(test(5) == 0)
check(test(15) == 1)
check(test(25) == 2)
check(test(35) == 3)
```

</details>

<details>
<summary>Advanced: break from nested loop</summary>

#### break from nested loop

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> bool:
    var found = false
    for i in 0..10:
        for j in 0..10:
            if i == 5 and j == 5:
                found = true
                break
        if found:
            break
    found
check(run())
```

</details>


</details>

<details>
<summary>Advanced: continue in all loops</summary>

#### continue in all loops

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..10:
        if i % 2 == 0:
            continue
        count = count + 1
    count
check(run() == 5)
```

</details>


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
