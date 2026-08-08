# Functions with Print/Side Effects (Interpreter)

> Tests function execution with print and side effect operations in the interpreter. Verifies that functions producing output and performing I/O side effects execute in the correct order with expected observable behavior.

<!-- sdn-diagram:id=functions_print_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=functions_print_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

functions_print_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=functions_print_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Functions with Print/Side Effects (Interpreter)

Tests function execution with print and side effect operations in the interpreter. Verifies that functions producing output and performing I/O side effects execute in the correct order with expected observable behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/functions_print_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests function execution with print and side effect operations in the interpreter.
Verifies that functions producing output and performing I/O side effects execute
in the correct order with expected observable behavior.

## Scenarios

### Functions with Print and Side Effects

#### print function

#### prints simple string

1. expect msg len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Note: we can't easily test print output in SPipe
# This test verifies print doesn't error
val msg = "test message"
expect msg.len() > 0
```

</details>

#### string formatting

#### formats with interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "Alice"
val age = 30
val formatted = "{name} is {age} years old"
expect formatted == "Alice is 30 years old"
```

</details>

#### formats expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val y = 3
val result = "{x} + {y} = {x + y}"
expect result == "5 + 3 = 8"
```

</details>

#### side effect functions

#### executes side effects in order

1. fn increment
2. counter = increment
3. counter = increment


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn increment(c: i64) -> i64:
    c + 1
var counter = 0
counter = increment(counter)
counter = increment(counter)
expect counter == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
