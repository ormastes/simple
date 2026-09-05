# Control Flow - If/Else Specification

> Tests for conditional control flow using if/else statements.

<!-- sdn-diagram:id=control_flow_if_else_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=control_flow_if_else_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

control_flow_if_else_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=control_flow_if_else_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Control Flow - If/Else Specification

Tests for conditional control flow using if/else statements.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1001 |
| Category | Language |
| Status | In Progress |
| Source | `test/03_system/feature/usage/control_flow_if_else_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for conditional control flow using if/else statements.
Verifies correct evaluation of conditions and execution of appropriate branches.

## Scenarios

### Control Flow - If/Else

#### basic if statements

#### executes if body when condition is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
var result = 0
if x > 0:
    result = 10
expect result == 10
```

</details>

#### skips if body when condition is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -5
var result = 0
if x > 0:
    result = 10
expect result == 0
```

</details>

#### if-else statements

#### executes if body when condition is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
var result = ""
if x > 5:
    result = "greater"
else:
    result = "less"
expect result == "greater"
```

</details>

#### executes else body when condition is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
var result = ""
if x > 5:
    result = "greater"
else:
    result = "less"
expect result == "less"
```

</details>

#### nested if statements

#### handles nested if statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
var result = 0
if x > 5:
    if y > 15:
        result = 1
expect result == 1
```

</details>

#### handles nested if-else

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val y = 20
var result = 0
if x > 5:
    result = 1
else:
    if y > 15:
        result = 2
expect result == 2
```

</details>

#### if-else-if chains

#### evaluates first matching condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 15
var result = ""
if x < 10:
    result = "low"
else:
    if x < 20:
        result = "medium"
    else:
        result = "high"
expect result == "medium"
```

</details>

#### executes final else when no conditions match

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 100
var result = ""
if x < 10:
    result = "low"
else:
    if x < 20:
        result = "medium"
    else:
        result = "high"
expect result == "high"
```

</details>

#### if with boolean expressions

#### evaluates AND conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 5
val b = 10
var result = false
if a > 0 and b > 0:
    result = true
expect result == true
```

</details>

#### evaluates OR conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = -5
val b = 10
var result = false
if a > 0 or b > 0:
    result = true
expect result == true
```

</details>

#### evaluates NOT conditions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
var result = false
if not (x < 0):
    result = true
expect result == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
