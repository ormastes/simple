# Variables and Assignment (Interpreter)

> Tests variable declaration and assignment in the interpreter including val/var bindings, walrus operator, and scope rules. Verifies that variable mutations are correctly tracked and that immutability constraints are enforced.

<!-- sdn-diagram:id=variables_assignment_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=variables_assignment_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

variables_assignment_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=variables_assignment_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Variables and Assignment (Interpreter)

Tests variable declaration and assignment in the interpreter including val/var bindings, walrus operator, and scope rules. Verifies that variable mutations are correctly tracked and that immutability constraints are enforced.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | In Progress |
| Source | `test/03_system/feature/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests variable declaration and assignment in the interpreter including val/var
bindings, walrus operator, and scope rules. Verifies that variable mutations
are correctly tracked and that immutability constraints are enforced.

## Scenarios

### Variables and Assignment

#### val declarations

#### creates immutable binding with inferred type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
expect x == 42
```

</details>

#### creates immutable binding with explicit type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name: text = "Alice"
expect name == "Alice"
```

</details>

#### var declarations

#### allows reassignment of mutable binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
count = count + 1
expect count == 1
```

</details>

#### supports compound assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 10
total = total + 5
expect total == 15
```

</details>

#### type inference

#### infers integer type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val num = 100
expect num == 100
```

</details>

#### infers string type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "hello"
expect msg == "hello"
```

</details>

#### infers boolean type

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = true
expect flag == true
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
