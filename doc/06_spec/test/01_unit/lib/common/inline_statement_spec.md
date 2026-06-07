# Inline Statement Specification

> 1. fn get value

<!-- sdn-diagram:id=inline_statement_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=inline_statement_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

inline_statement_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=inline_statement_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Statement Specification

## Scenarios

### Inline statement in if

### return statement

#### supports inline return in function

1. fn get value
2. expect get value
3. expect get value
4. expect get value


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value(x: i64) -> i64:
    if x < 0: return -1
    if x == 0: return 0
    return 1

expect get_value(-5) == -1
expect get_value(0) == 0
expect get_value(5) == 1
```

</details>

#### supports inline return with expression

1. fn abs value
2. expect abs value
3. expect abs value
4. expect abs value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn abs_value(x: i64) -> i64:
    if x < 0: return -x
    return x

expect abs_value(-10) == 10
expect abs_value(10) == 10
expect abs_value(0) == 0
```

</details>

#### supports inline return in multiple conditions

1. fn classify
2. expect classify
3. expect classify
4. expect classify
5. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    if x < 0: return "negative"
    if x == 0: return "zero"
    if x > 100: return "large"
    return "positive"

expect classify(-5) == "negative"
expect classify(0) == "zero"
expect classify(50) == "positive"
expect classify(200) == "large"
```

</details>

### break statement

<details>
<summary>Advanced: supports inline break in loop</summary>

#### supports inline break in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
var i = 0
while i < 100:
    if i >= 5: break
    sum = sum + i
    i = i + 1

expect sum == 10  # 0+1+2+3+4 = 10
expect i == 5
```

</details>


</details>

<details>
<summary>Advanced: supports inline break in for loop</summary>

#### supports inline break in for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for x in [1, 2, 3, 4, 5]:
    if x > 3: break
    count = count + 1

expect count == 3
```

</details>


</details>

### continue statement

<details>
<summary>Advanced: supports inline continue in loop</summary>

#### supports inline continue in loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for x in [1, 2, 3, 4, 5]:
    if x == 3: continue
    sum = sum + x

expect sum == 12  # 1+2+4+5 = 12
```

</details>


</details>

#### supports inline continue skipping multiple values

1. result = result push


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = []
for x in [1, 2, 3, 4, 5, 6]:
    if x % 2 == 0: continue
    result = result.push(x)

expect result == [1, 3, 5]
```

</details>

### combined with regular if

#### works with elif and else blocks

1. fn categorize
2. expect categorize
3. expect categorize
4. expect categorize


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn categorize(x: i64) -> text:
    if x < 0: return "negative"
    elif x == 0:
        return "zero"
    else:
        return "positive"

expect categorize(-1) == "negative"
expect categorize(0) == "zero"
expect categorize(1) == "positive"
```

</details>

#### allows inline if without else when using statement

1. fn early return
2. expect early return
3. expect early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn early_return(x: i64) -> i64:
    if x < 0: return 0
    # This line is reached only for non-negative x
    return x * 2

expect early_return(-5) == 0
expect early_return(5) == 10
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/inline_statement_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Inline statement in if
- return statement
- break statement
- continue statement
- combined with regular if

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
