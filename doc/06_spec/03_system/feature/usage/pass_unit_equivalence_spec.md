# Pass Statement and Unit Value Equivalence

> In Simple, the `pass` keyword and the unit literal `()` are semantically equivalent -- both represent a deliberate no-operation and compile to the same code. This spec proves their interchangeability in every statement position: standalone expressions, if/else branches, and loop bodies. It also documents the style guideline that `pass` is preferred when the programmer wants to signal explicit "do nothing" intent, while `()` is the underlying unit value.

<!-- sdn-diagram:id=pass_unit_equivalence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pass_unit_equivalence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pass_unit_equivalence_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pass_unit_equivalence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pass Statement and Unit Value Equivalence

In Simple, the `pass` keyword and the unit literal `()` are semantically equivalent -- both represent a deliberate no-operation and compile to the same code. This spec proves their interchangeability in every statement position: standalone expressions, if/else branches, and loop bodies. It also documents the style guideline that `pass` is preferred when the programmer wants to signal explicit "do nothing" intent, while `()` is the underlying unit value.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LANG-021 |
| Category | Language |
| Status | Active |
| Source | `test/03_system/feature/usage/pass_unit_equivalence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

In Simple, the `pass` keyword and the unit literal `()` are semantically
equivalent -- both represent a deliberate no-operation and compile to the same
code. This spec proves their interchangeability in every statement position:
standalone expressions, if/else branches, and loop bodies. It also documents the
style guideline that `pass` is preferred when the programmer wants to signal
explicit "do nothing" intent, while `()` is the underlying unit value.

## Syntax

```simple
# pass as a standalone no-op
pass
x = 1

# () as a standalone no-op
()
x = 1

# pass inside an if-else branch
if x == 10:
branch_taken = "ten"
else:
pass
branch_taken = "other"

# pass inside a loop body
for i in [0, 1, 2]:
if i == 1:
pass
count = count + 1
```

## Key Concepts

| Concept | Description |
|---------|-------------|
| `pass` | A no-op keyword signalling intentional emptiness, analogous to Python's `pass` |
| `()` | The unit literal, representing the absence of a meaningful value |
| Equivalence | `pass` and `()` produce identical compiled output in all statement positions |
| Style guideline | Use `pass` for explicit no-op intent; use `()` when a unit value is needed |

## Scenarios

### pass and () equivalence

#### both work as standalone statements

1.


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var executed = false

# With pass
pass
executed = true
expect executed == true

# With ()
executed = false
()
executed = true
expect executed == true
```

</details>

#### both work in if-else branches

1.


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
var branch_taken = ""

# Using pass
if x == 10:
    branch_taken = "ten"
else:
    pass
    branch_taken = "other"

expect branch_taken == "other"

# Using ()
branch_taken = ""
if x == 10:
    branch_taken = "ten"
else:
    ()
    branch_taken = "other"

expect branch_taken == "other"
```

</details>

<details>
<summary>Advanced: both work in loops</summary>

#### both work in loops

1.


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0

# With pass
for i in [0, 1, 2]:
    if i == 1:
        pass
    count = count + 1

expect count == 3

# With ()
count = 0
for i in [0, 1, 2]:
    if i == 1:
        ()
    count = count + 1

expect count == 3
```

</details>


</details>

### pass and () documentation

#### documents that pass is no-op statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 0
pass
x = 1
expect x == 1
```

</details>

### style guidelines

#### recommends pass for explicit no-op intent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var logged = false
if true:
    pass
    logged = false
expect logged == false
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
