# Control Flow (Interpreter)

> Tests control flow constructs in the interpreter including if/else, match, for/while loops, and early returns. Verifies that branching, iteration, and loop control statements execute with correct semantics in interpreted mode.

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
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control Flow (Interpreter)

Tests control flow constructs in the interpreter including if/else, match, for/while loops, and early returns. Verifies that branching, iteration, and loop control statements execute with correct semantics in interpreted mode.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/control_flow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests control flow constructs in the interpreter including if/else, match, for/while
loops, and early returns. Verifies that branching, iteration, and loop control
statements execute with correct semantics in interpreted mode.

## Scenarios

### eval_for

#### iterable evaluation

<details>
<summary>Advanced: evaluates iterable before loop</summary>

#### evaluates iterable before loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
val items = [1, 2, 3]
for x in items:
    result = result + x
expect result == 6
```

</details>


</details>

#### evaluates range expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 1..5:
    sum = sum + i
expect sum == 10
```

</details>

#### loop variable scope

<details>
<summary>Advanced: creates new scope for loop variable</summary>

#### creates new scope for loop variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
for x in [1, 2, 3]:
    pass
expect x == 100
```

</details>


</details>

<details>
<summary>Advanced: binds loop variable for each iteration</summary>

#### binds loop variable for each iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var last = 0
for i in [5, 10, 15]:
    last = i
expect last == 15
```

</details>


</details>

#### control flow signals

#### handles break with value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..10:
    count = count + 1
    if i == 5:
        break
expect count == 6
```

</details>

#### handles continue signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    if i == 2:
        continue
    sum = sum + i
expect sum == 8
```

</details>

### eval_while

#### condition evaluation

#### checks condition before each iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
var count = 0
while i < 3:
    count = count + 1
    i = i + 1
expect count == 3
```

</details>

#### does not execute body if condition is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false
while false:
    executed = true
expect not executed
```

</details>

#### control flow signals

#### handles continue signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
var i = 0
while i < 5:
    i = i + 1
    if i == 3:
        continue
    sum = sum + i
expect sum == 12
```

</details>

#### handles break signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
while true:
    count = count + 1
    if count == 5:
        break
expect count == 5
```

</details>

### eval_loop

#### break signal

#### breaks on Break signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var iterations = 0
loop:
    iterations = iterations + 1
    if iterations >= 3:
        break
expect iterations == 3
```

</details>

#### can break with computed condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var n = 10
loop:
    n = n - 1
    if n == 0:
        break
expect n == 0
```

</details>

### eval_if

#### condition evaluation

#### evaluates true condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true: 1 else: 0
expect result == 1
```

</details>

#### evaluates false condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if false: 1 else: 0
expect result == 0
```

</details>

#### evaluates comparison expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val result = if x > 5: 1 else: 0
expect result == 1
```

</details>

#### branch execution

#### executes then branch when true

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = "none"
if true:
    executed = "then"
else:
    executed = "else"
expect executed == "then"
```

</details>

#### executes else branch when false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = "none"
if false:
    executed = "then"
else:
    executed = "else"
expect executed == "else"
```

</details>

### eval_match

#### tuple matching

#### matches tuple and binds variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, 2)
val result = match t:
    case (1, x): x * 10
    case _: 0
expect result == 20
```

</details>

#### uses wildcard for unmatched patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (5, 5)
val result = match t:
    case (1, x): x
    case _: 99
expect result == 99
```

</details>

#### array matching

#### matches array and binds elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [5, 10]
val result = match arr:
    case [a, b]: a + b
    case _: 0
expect result == 15
```

</details>

#### handles array length mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
val result = match arr:
    case [a, b]: a + b
    case _: -1
expect result == -1
```

</details>

### Control Flow Integration

#### nests for inside while

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
var outer = 0
while outer < 2:
    for i in 0..3:
        sum = sum + 1
    outer = outer + 1
expect sum == 6
```

</details>

#### nests if inside for

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var evens = 0
for i in 0..10:
    if i % 2 == 0:
        evens = evens + 1
expect evens == 5
```

</details>

#### combines match with for

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
val items = [(1, 10), (2, 20), (3, 30)]
for item in items:
    val add = match item:
        case (1, x): x
        case (2, x): x * 2
        case _: 0
    sum = sum + add
expect sum == 50
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
