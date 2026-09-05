# If Else Implicit Return Specification

> 1. fn get sign

<!-- sdn-diagram:id=if_else_implicit_return_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=if_else_implicit_return_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

if_else_implicit_return_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=if_else_implicit_return_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# If Else Implicit Return Specification

## Scenarios

### If-else implicit return

### basic if-else

#### returns value from if branch

1. fn get sign
2. expect get sign
3. expect get sign


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_sign(x: i64) -> text:
    if x >= 0:
        "positive"
    else:
        "negative"

expect get_sign(5) == "positive"
expect get_sign(-5) == "negative"
```

</details>

#### returns value from else branch

1. fn is even
2. expect is even
3. expect is even


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn is_even(x: i64) -> bool:
    if x % 2 == 0:
        true
    else:
        false

expect is_even(4) == true
expect is_even(3) == false
```

</details>

#### returns complex expressions

1. fn double or triple
2. expect double or triple
3. expect double or triple


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double_or_triple(x: i64, double: bool) -> i64:
    if double:
        x * 2
    else:
        x * 3

expect double_or_triple(5, true) == 10
expect double_or_triple(5, false) == 15
```

</details>

### if-elif-else chain

#### returns from elif branch

1. fn classify
2. expect classify
3. expect classify
4. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    if x < 0:
        "negative"
    elif x == 0:
        "zero"
    else:
        "positive"

expect classify(-5) == "negative"
expect classify(0) == "zero"
expect classify(5) == "positive"
```

</details>

#### returns from multiple elif branches

1. fn grade
2. expect grade
3. expect grade
4. expect grade
5. expect grade
6. expect grade


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn grade(score: i64) -> text:
    if score >= 90:
        "A"
    elif score >= 80:
        "B"
    elif score >= 70:
        "C"
    elif score >= 60:
        "D"
    else:
        "F"

expect grade(95) == "A"
expect grade(85) == "B"
expect grade(75) == "C"
expect grade(65) == "D"
expect grade(55) == "F"
```

</details>

### nested if-else

#### returns from nested if-else

1. fn nested check
2. expect nested check
3. expect nested check
4. expect nested check
5. expect nested check


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn nested_check(a: bool, b: bool) -> text:
    if a:
        if b:
            "both"
        else:
            "only a"
    else:
        if b:
            "only b"
        else:
            "neither"

expect nested_check(true, true) == "both"
expect nested_check(true, false) == "only a"
expect nested_check(false, true) == "only b"
expect nested_check(false, false) == "neither"
```

</details>

### with other statements before

#### returns after variable declaration

1. fn add with check
2. expect add with check
3. expect add with check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add_with_check(a: i64, b: i64) -> i64:
    val sum = a + b
    if sum > 100:
        100
    else:
        sum

expect add_with_check(30, 40) == 70
expect add_with_check(80, 50) == 100
```

</details>

<details>
<summary>Advanced: returns after loop</summary>

#### returns after loop

1. fn sum until
2. expect sum until
3. expect sum until


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_until(limit: i64) -> i64:
    var total = 0
    var i = 1
    while i <= limit:
        total = total + i
        i = i + 1
    if total > 100:
        100
    else:
        total

expect sum_until(5) == 15
expect sum_until(20) == 100
```

</details>


</details>

### return type inference

#### works with integer return

1. fn max val
2. expect max val
3. expect max val


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn max_val(a: i64, b: i64) -> i64:
    if a > b:
        a
    else:
        b

expect max_val(10, 5) == 10
expect max_val(5, 10) == 10
```

</details>

#### works with text return

1. fn greeting
2. expect greeting
3. expect greeting


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greeting(formal: bool) -> text:
    if formal:
        "Good day"
    else:
        "Hi"

expect greeting(true) == "Good day"
expect greeting(false) == "Hi"
```

</details>

#### works with boolean return

1. fn both positive
2. expect both positive
3. expect both positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn both_positive(a: i64, b: i64) -> bool:
    if a > 0 and b > 0:
        true
    else:
        false

expect both_positive(1, 2) == true
expect both_positive(-1, 2) == false
```

</details>

### mixed with explicit return

#### works with early return and implicit else

1. fn absolute
2. expect absolute
3. expect absolute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn absolute(x: i64) -> i64:
    if x < 0:
        return -x
    x

expect absolute(-5) == 5
expect absolute(5) == 5
```

</details>

#### works with guard clause pattern

1. fn safe divide
2. expect safe divide
3. expect safe divide
4. expect safe divide


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn safe_divide(a: i64, b: i64) -> i64:
    if b == 0:
        return 0
    if a < 0:
        -1
    else:
        a / b

expect safe_divide(10, 2) == 5
expect safe_divide(10, 0) == 0
expect safe_divide(-10, 2) == -1
```

</details>

### with function calls

#### returns function call result

1. fn double
2. fn conditional double
3. double
4. expect conditional double
5. expect conditional double


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2

fn conditional_double(x: i64, should_double: bool) -> i64:
    if should_double:
        double(x)
    else:
        x

expect conditional_double(5, true) == 10
expect conditional_double(5, false) == 5
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/if_else_implicit_return_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- If-else implicit return
- basic if-else
- if-elif-else chain
- nested if-else
- with other statements before
- return type inference
- mixed with explicit return
- with function calls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
