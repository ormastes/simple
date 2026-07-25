# Default Arguments Specification

> Tests for function default argument values.

<!-- sdn-diagram:id=default_arguments_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=default_arguments_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

default_arguments_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=default_arguments_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Default Arguments Specification

Tests for function default argument values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DEFARG-001 |
| Category | Language \| Functions |
| Status | Implemented |
| Source | `test/03_system/feature/usage/default_arguments_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for function default argument values.

## Syntax

```simple
fn greet(name, greeting="Hello"):
print "{greeting}, {name}!"

greet("Alice")           # Uses default: "Hello, Alice!"
greet("Bob", "Hi")       # Override: "Hi, Bob!"
```

## Scenarios

### Default Arguments

#### uses default argument when not provided

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b=10):
    return a + b

expect add(5) == 15
```

</details>

#### overrides default argument when provided

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b=10):
    return a + b

expect add(5, b=20) == 25
```

</details>

#### uses multiple default arguments

1. fn calc
2. expect calc


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn calc(a, b=2, c=3):
    return a + b * c

expect calc(1) == 7
```

</details>

#### overrides some default arguments

1. fn calc
2. expect calc


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn calc(a, b=2, c=3):
    return a + b * c

expect calc(1, c=10) == 21
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
