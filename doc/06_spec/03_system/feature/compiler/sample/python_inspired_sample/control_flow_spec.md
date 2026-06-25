# Control Flow (Python-Inspired Sample)

> Tests compilation of control flow constructs inspired by Python including if/else, for loops, while loops, and match expressions. Verifies that indentation-based control flow compiles correctly through the native pipeline.

<!-- sdn-diagram:id=control_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=control_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

control_flow_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=control_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control Flow (Python-Inspired Sample)

Tests compilation of control flow constructs inspired by Python including if/else, for loops, while loops, and match expressions. Verifies that indentation-based control flow compiles correctly through the native pipeline.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/control_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of control flow constructs inspired by Python including if/else,
for loops, while loops, and match expressions. Verifies that indentation-based
control flow compiles correctly through the native pipeline.

## Scenarios

### Control Flow

#### if/else

#### executes if branch when true

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
var result = ""
if x > 5:
    result = "big"
else:
    result = "small"
expect result == "big"
```

</details>

#### executes else branch when false

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
var result = ""
if x > 5:
    result = "big"
else:
    result = "small"
expect result == "small"
```

</details>

#### for loops

#### iterates over range

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

#### iterates over list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["a", "b", "c"]
var count = 0
for item in items:
    count = count + 1
expect count == 3
```

</details>

#### while loops

<details>
<summary>Advanced: loops while condition is true</summary>

#### loops while condition is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
var sum = 0
while i < 5:
    sum = sum + i
    i = i + 1
expect sum == 10
```

</details>


</details>

#### match expressions

#### matches literal values

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val result = match x:
    case 1:
        "one"
    case 2:
        "two"
    case _:
        "other"
expect result == "two"
```

</details>

#### matches with guards

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 15
val category = match n:
    case x if x > 10:
        "large"
    case x if x > 0:
        "small"
    case _:
        "non-positive"
expect category == "large"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
