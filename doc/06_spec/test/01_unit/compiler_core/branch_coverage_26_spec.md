# Branch Coverage Test Suite - Parser Error Paths

> Tests error handling and edge case branches in parser. Improves seed compiler coverage by exercising error paths.

<!-- sdn-diagram:id=branch_coverage_26_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_26_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_26_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_26_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Parser Error Paths

Tests error handling and edge case branches in parser. Improves seed compiler coverage by exercising error paths.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #PARSER #ERROR_HANDLING |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_26_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests error handling and edge case branches in parser.
Improves seed compiler coverage by exercising error paths.

## Scenarios

### Parser Error Handling Coverage

#### handles empty input gracefully

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Tests parser with minimal input
val result = 0 + 0
check(result == 0)
```

</details>

#### handles single token

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
check(x == 42)
```

</details>

#### handles maximum nesting depth

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Deeply nested parentheses
val result = ((((((((1))))))))
check(result == 1)
```

</details>

#### handles long identifier names

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val very_long_variable_name_that_tests_buffer_limits_in_lexer = 123
check(very_long_variable_name_that_tests_buffer_limits_in_lexer == 123)
```

</details>

#### handles edge case - negative zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -0
check(x == 0)
```

</details>

#### handles edge case - empty string

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
check(s.len() == 0)
```

</details>

#### handles edge case - string with only escape

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "\n"
check(s.len() > 0)
```

</details>

#### handles multiple string interpolations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 1
val b = 2
val s = "{a} and {b}"
check(s.contains("1"))
```

</details>

#### handles nested string interpolations

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val s = "value: {x + 10}"
check(s.contains("15"))
```

</details>

### Expression Edge Cases Coverage

#### handles precedence - multiplication before addition

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 + 3 * 4
check(result == 14)
```

</details>

#### handles precedence - parentheses override

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (2 + 3) * 4
check(result == 20)
```

</details>

#### handles unary negation with expression

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -(5 + 3)
check(result == -8)
```

</details>

#### handles double negation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = -(-10)
check(result == 10)
```

</details>

#### handles not operator

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = not false
check(result == true)
```

</details>

#### handles not with comparison

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = not (5 > 10)
check(result == true)
```

</details>

#### handles chain comparisons - all true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 < 2 and 2 < 3
check(result == true)
```

</details>

#### handles chain comparisons - one false

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 1 < 2 and 2 > 3
check(result == false)
```

</details>

### Match Statement Edge Cases Coverage

#### match with single case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val result = match x:
    1: "one"
    _: "other"
check(result == "one")
```

</details>

#### match with no default - nil case

1. Some
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(5)
match x:
    Some(v):
        check(v == 5)
    nil:
        check(false)
```

</details>

#### match with wildcard only

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
val result = match x:
    _: "always"
check(result == "always")
```

</details>

#### match with boolean patterns

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = true
val result = match b:
    true: 1
    false: 0
check(result == 1)
```

</details>

### Loop Edge Cases Coverage

<details>
<summary>Advanced: for loop with zero iterations</summary>

#### for loop with zero iterations

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


</details>

<details>
<summary>Advanced: for loop with one iteration</summary>

#### for loop with one iteration

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..1:
    count = count + 1
check(count == 1)
```

</details>


</details>

<details>
<summary>Advanced: for loop with negative range handled</summary>

#### for loop with negative range handled

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 5..5:
    count = count + 1
check(count == 0)
```

</details>


</details>

<details>
<summary>Advanced: while loop never enters</summary>

#### while loop never enters

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false
while false:
    executed = true
check(executed == false)
```

</details>


</details>

<details>
<summary>Advanced: while loop with immediate break</summary>

#### while loop with immediate break

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    while true:
        count = count + 1
        break
    count
check(run() == 1)
```

</details>


</details>

<details>
<summary>Advanced: nested loops with break in inner</summary>

#### nested loops with break in inner

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var outer_count = 0
    var inner_count = 0
    for i in 0..3:
        outer_count = outer_count + 1
        for j in 0..3:
            inner_count = inner_count + 1
            break
    outer_count * 10 + inner_count
check(run() == 33)
```

</details>


</details>

### Optional Chaining Edge Cases Coverage

#### optional chain with nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64? = nil
val result = x ?? 99
check(result == 99)
```

</details>

#### optional chain with value

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64? = Some(42)
val result = x ?? 99
check(result == 42)
```

</details>

#### nested optional with nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
check(not x.?)
```

</details>

#### nested optional with some

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(Some(10))
check(x.?)
```

</details>

### Array Edge Cases Coverage

#### empty array creation

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = []
check(arr.len() == 0)
```

</details>

#### array with one element

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [42]
check(arr.len() == 1)
check(arr[0] == 42)
```

</details>

#### array negative index

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(arr[-1] == 3)
check(arr[-2] == 2)
```

</details>

#### array slice empty result

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(slice_len(arr, 0, 0) == 0)
```

</details>

#### array slice full

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(slice_len(arr, 0, 3) == 3)
```

</details>

### Type Edge Cases Coverage

#### boolean true literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true == true)
```

</details>

#### boolean false literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(false == false)
```

</details>

#### nil literal type

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
check(not x.?)
```

</details>

#### integer zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(0 == 0)
```

</details>

#### integer negative

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(-1 < 0)
```

</details>

#### integer positive

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 > 0)
```

</details>

#### float zero

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: f64 = 0.0
check(f == 0.0)
```

</details>

#### float negative

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: f64 = -1.5
check(f < 0.0)
```

</details>

#### float positive

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: f64 = 1.5
check(f > 0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
