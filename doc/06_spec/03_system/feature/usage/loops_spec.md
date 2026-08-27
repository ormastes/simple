# Loop Constructs Specification

> var i = 0

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
| Updated | 2026-08-26 |
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

- executes while loop with condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes while loop with condition")
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

- exits while loop when condition becomes false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exits while loop when condition becomes false")
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

- handles while loop with break


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles while loop with break")
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

- handles while loop with continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles while loop with continue")
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

- iterates over exclusive range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over exclusive range")
var sum = 0
for i in 0..5:
    sum = sum + i
expect sum == 10
```

</details>

#### iterates over inclusive range

- iterates over inclusive range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over inclusive range")
var sum = 0
for i in 0..=5:
    sum = sum + i
expect sum == 15
```

</details>

#### handles negative ranges

- handles negative ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles negative ranges")
var sum = 0
for i in -3..=0:
    sum = sum + i
expect sum == -6
```

</details>

#### for loops over collections

#### iterates over list

- iterates over list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates over list")
val items = [1, 2, 3, 4, 5]
var sum = 0
for item in items:
    sum = sum + item
expect sum == 15
```

</details>

#### iterates with break

- iterates with break


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates with break")
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

- iterates with continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates with continue")
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

- executes nested loops


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes nested loops")
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

- breaks outer loop from nested loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("breaks outer loop from nested loop")
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

- creates list from range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates list from range")
val result = [for x in 0..5: x * 2]
expect result == [0, 2, 4, 6, 8]
```

</details>

#### filters with comprehension

- filters with comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters with comprehension")
val result = [for x in 0..10 if x % 2 == 0: x]
expect result == [0, 2, 4, 6, 8]
```

</details>

#### transforms and filters

- transforms and filters


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("transforms and filters")
val result = [for x in 1..6 if x > 2: x * 2]
expect result == [6, 8, 10]
```

</details>

#### comprehension over existing collection

- comprehension over existing collection


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("comprehension over existing collection")
val items = [1, 2, 3, 4, 5]
val result = [for x in items: x * 2]
expect result == [2, 4, 6, 8, 10]
```

</details>

#### range with step

#### iterates with positive step

- iterates with positive step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates with positive step")
val result = [for x in range(0, 10, 2): x]
expect result == [0, 2, 4, 6, 8]
```

</details>

#### iterates with negative step

- iterates with negative step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("iterates with negative step")
val result = [for x in range(5, 0, -1): x]
expect result == [5, 4, 3, 2, 1]
```

</details>

#### dictionary comprehension

#### creates dict from range

- creates dict from range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates dict from range")
val result = {for x in 0..3: (x, x * 2)}
expect result[0] == 0
expect result[1] == 2
expect result[2] == 4
```

</details>

#### complex loop patterns

#### nested comprehension

- nested comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested comprehension")
val matrix = [[1, 2], [3, 4], [5, 6]]
val result = [for row in matrix: [for cell in row: cell * 2]]
expect result == [[2, 4], [6, 8], [10, 12]]
```

</details>

#### conditional nesting in comprehension

- conditional nesting in comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("conditional nesting in comprehension")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `60262785071694b13827ac9733c586ee44a3edfa906e9f5f4746be4ddd2a4885`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `60262785071694b13827ac9733c586ee44a3edfa906e9f5f4746be4ddd2a4885`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `60262785071694b13827ac9733c586ee44a3edfa906e9f5f4746be4ddd2a4885`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/loops_spec.spl
mirror: doc/06_spec/03_system/feature/usage/loops_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/loops_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/loops_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/loops_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes while loop with condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/loops_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exits while loop when condition becomes false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/loops_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles while loop with break' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
