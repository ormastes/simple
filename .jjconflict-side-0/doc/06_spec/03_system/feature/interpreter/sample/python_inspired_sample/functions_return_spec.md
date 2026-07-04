# Functions with Return Values (Interpreter)

> Tests function return value handling in the interpreter including explicit returns, implicit last-expression returns, and multi-value returns. Verifies that return values are correctly propagated through the call stack.

<!-- sdn-diagram:id=functions_return_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=functions_return_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

functions_return_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=functions_return_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Functions with Return Values (Interpreter)

Tests function return value handling in the interpreter including explicit returns, implicit last-expression returns, and multi-value returns. Verifies that return values are correctly propagated through the call stack.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/functions_return_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests function return value handling in the interpreter including explicit returns,
implicit last-expression returns, and multi-value returns. Verifies that return
values are correctly propagated through the call stack.

## Scenarios

### Functions with Return Values

#### implicit return

#### returns last expression

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2
expect double(5) == 10
```

</details>

#### returns computed value

1. fn square
2. expect square


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(n: i64) -> i64:
    n * n
expect square(4) == 16
```

</details>

#### explicit return

#### returns early from function

1. fn classify
2. expect classify
3. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    if x < 0:
        return "negative"
    "non-negative"
expect classify(-5) == "negative"
expect classify(5) == "non-negative"
```

</details>

#### return type inference

#### infers integer return type

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64):
    a + b
expect add(3, 4) == 7
```

</details>

#### infers string return type

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text):
    "Hello, {name}!"
expect greet("World") == "Hello, World!"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
