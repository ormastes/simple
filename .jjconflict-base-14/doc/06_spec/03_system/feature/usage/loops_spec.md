# Loop Constructs Specification

> var i = 0

<!-- sdn-diagram:id=loops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loops_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loop Constructs Specification

var i = 0

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1100 |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/loops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# While loop (condition-based)
var i = 0
while i < 10:
print i
i = i + 1

# For loop (collection iteration)
for item in items:
print item

# Range iteration
for i in 0..10:
print i

# List comprehension
[for x in items if x > 5: x * 2]

# Dictionary comprehension
{for x in items: (x, x * 2)}
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| While Loop | Condition-based repetition until condition becomes false |
| For Loop | Iteration over collection elements with implicit binding |
| Range | Sequence of values from start to end (inclusive or exclusive) |
| Comprehension | Concise syntax for building collections from iterations |
| Break Statement | Exit loop immediately |
| Continue Statement | Skip to next loop iteration |

## Behavior

Loop constructs:
- Execute code zero or more times based on conditions or collection size
- Support break and continue for flow control
- Provide implicit iteration variables in for loops
- Enable collection creation through comprehensions
- Work with ranges and user-defined iterables
- Support nested loops and complex conditions

## Related Specifications

- Range Expressions (start..end syntax)
- Collection Types (List, Dict, Set iteration)
- Pattern Matching (destructuring in for loops)
- Lambda Expressions (used in functional iteration)

## Scenarios

### Loop Constructs

#### while loops

<details>
<summary>Advanced: executes while loop with condition</summary>

#### executes while loop with condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
var i = 0
while i < 5:
    count = count + 1
    i = i + 1
expect count == 5
```

</details>


</details>

<details>
<summary>Advanced: exits while loop when condition becomes false</summary>

#### exits while loop when condition becomes false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
var i = 1
while i <= 4:
    total = total + i
    i = i + 1
expect total == 10
```

</details>


</details>

<details>
<summary>Advanced: handles while loop with break</summary>

#### handles while loop with break

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
var count = 0
while true:
    count = count + 1
    i = i + 1
    if i == 5:
        break
expect count == 5
```

</details>


</details>

<details>
<summary>Advanced: handles while loop with continue</summary>

#### handles while loop with continue

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


</details>

#### for loops over ranges

#### iterates over exclusive range

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

#### iterates over inclusive range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..=5:
    sum = sum + i
expect sum == 15
```

</details>

#### handles negative ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in -3..=0:
    sum = sum + i
expect sum == -6
```

</details>

#### for loops over collections

#### iterates over list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
var sum = 0
for item in items:
    sum = sum + item
expect sum == 15
```

</details>

#### iterates with break

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
var sum = 0
for item in items:
    if item == 3:
        break
    sum = sum + item
expect sum == 3
```

</details>

#### iterates with continue

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
var sum = 0
for item in items:
    if item == 3:
        continue
    sum = sum + item
expect sum == 12
```

</details>

#### nested loops

<details>
<summary>Advanced: executes nested loops</summary>

#### executes nested loops

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..3:
    for j in 0..3:
        sum = sum + 1
expect sum == 9
```

</details>


</details>

<details>
<summary>Advanced: breaks outer loop from nested loop</summary>

#### breaks outer loop from nested loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    for j in 0..5:
        sum = sum + 1
        if sum == 6:
            break
    if sum == 6:
        break
expect sum == 6
```

</details>


</details>

#### list comprehensions

#### creates list from range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in 0..5: x * 2]
expect result == [0, 2, 4, 6, 8]
```

</details>

#### filters with comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in 0..10 if x % 2 == 0: x]
expect result == [0, 2, 4, 6, 8]
```

</details>

#### transforms and filters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in 1..6 if x > 2: x * 2]
expect result == [6, 8, 10]
```

</details>

#### comprehension over existing collection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3, 4, 5]
val result = [for x in items: x * 2]
expect result == [2, 4, 6, 8, 10]
```

</details>

#### range with step

#### iterates with positive step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in range(0, 10, 2): x]
expect result == [0, 2, 4, 6, 8]
```

</details>

#### iterates with negative step

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in range(5, 0, -1): x]
expect result == [5, 4, 3, 2, 1]
```

</details>

#### dictionary comprehension

#### creates dict from range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = {for x in 0..3: (x, x * 2)}
expect result[0] == 0
expect result[1] == 2
expect result[2] == 4
```

</details>

#### complex loop patterns

#### nested comprehension

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = [[1, 2], [3, 4], [5, 6]]
val result = [for row in matrix: [for cell in row: cell * 2]]
expect result == [[2, 4], [6, 8], [10, 12]]
```

</details>

#### conditional nesting in comprehension

1. expect result len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [for x in 0..5 if x > 1: [for y in 0..2: x + y]]
expect result.len() == 3
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
