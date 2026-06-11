# Control Flow Patterns (Interpreter Sample)

> Tests Python-inspired control flow patterns in the interpreter including if/elif/else chains, while loops with break/continue, and for-in iteration. Verifies that indentation-based control flow works correctly in interpreted mode.

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

# Control Flow Patterns (Interpreter Sample)

Tests Python-inspired control flow patterns in the interpreter including if/elif/else chains, while loops with break/continue, and for-in iteration. Verifies that indentation-based control flow works correctly in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/control_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests Python-inspired control flow patterns in the interpreter including if/elif/else
chains, while loops with break/continue, and for-in iteration. Verifies that
indentation-based control flow works correctly in interpreted mode.

## Scenarios

### Control Flow

#### if expressions

#### evaluates then branch when true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true: "yes" else: "no"
expect result == "yes"
```

</details>

#### evaluates else branch when false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if false: "yes" else: "no"
expect result == "no"
```

</details>

#### chains elif conditions

1. fn classify
2. expect classify
3. expect classify
4. expect classify


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn classify(x: i64) -> text:
    if x > 0:
        "positive"
    elif x < 0:
        "negative"
    else:
        "zero"
expect classify(5) == "positive"
expect classify(-5) == "negative"
expect classify(0) == "zero"
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
val items = [1, 2, 3]
var total = 0
for item in items:
    total = total + item
expect total == 6
```

</details>

#### while loops

<details>
<summary>Advanced: loops while condition true</summary>

#### loops while condition true

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

#### match expressions

#### matches literal pattern

1. fn describe
2. expect describe
3. expect describe
4. expect describe


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn describe(x: i64) -> text:
    match x:
        case 0:
            "zero"
        case 1:
            "one"
        case _:
            "other"
expect describe(0) == "zero"
expect describe(1) == "one"
expect describe(99) == "other"
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
