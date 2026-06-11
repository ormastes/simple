# Type Checking Specification

> 1. fn add

<!-- sdn-diagram:id=type_checking_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_checking_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_checking_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_checking_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Checking Specification

## Scenarios

### Function Parameter Type Checking

#### passes when types match

1. fn add
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(x: i64, y: i64) -> i64:
    x + y
val result = add(5, 10)
expect(result).to_equal(15)
```

</details>

#### accepts bool parameter

1. fn is true
   - Expected: result is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn is_true(flag: bool) -> bool:
    flag
val result = is_true(true)
expect(result).to_equal(true)
```

</details>

#### accepts text parameter

1. fn greet
   - Expected: result equals `Hello, World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text) -> text:
    "Hello, " + name
val result = greet("World")
expect(result).to_equal("Hello, World")
```

</details>

#### accepts f64 parameter

1. fn double
   - Expected: result equals `7.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: f64) -> f64:
    x * 2.0
val result = double(3.5)
expect(result).to_equal(7.0)
```

</details>

#### works with multiple typed parameters

1. fn combine
2. txt + " " + str
3. str
   - Expected: result equals `answer 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn combine(num: i64, txt: text, flag: bool) -> text:
    if flag:
        txt + " " + str(num)
    else:
        str(num) + " " + txt
val result = combine(42, "answer", true)
expect(result).to_equal("answer 42")
```

</details>

#### works with untyped parameters

1. fn identity
   - Expected: result equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x):
    x
val result = identity(123)
expect(result).to_equal(123)
```

</details>

### Type Checking Edge Cases

#### handles nil values

1. fn maybe
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn maybe(x) -> i64:
    if x == nil:
        0
    else:
        x
val result = maybe(nil)
expect(result).to_equal(0)
```

</details>

#### works with nested function calls

1. fn inner
2. fn outer
3. inner
   - Expected: result equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inner(x: i64) -> i64:
    x + 1
fn outer(y: i64) -> i64:
    inner(y) * 2
val result = outer(5)
expect(result).to_equal(12)
```

</details>

#### accepts array parameters

1. fn sum array
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_array(arr) -> i64:
    var total: i64 = 0
    for x in arr:
        total = total + x
    total
val result = sum_array([1, 2, 3, 4, 5])
expect(result).to_equal(15)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/interpreter/type_checking_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Function Parameter Type Checking
- Type Checking Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
