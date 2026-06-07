# Guard Clause Specification

> <details>

<!-- sdn-diagram:id=guard_clause_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=guard_clause_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

guard_clause_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=guard_clause_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guard Clause Specification

## Scenarios

### guard clauses

### basic guard evaluation

#### guard true: matches arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val result = match x:
    case 5 if x > 3: "big_five"
    case 5: "five"
    case _: "other"
expect(result).to_equal("big_five")
```

</details>

#### guard false: falls to next arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
val result = match x:
    case 5 if x > 10: "big_five"
    case 5: "five"
    case _: "other"
expect(result).to_equal("five")
```

</details>

#### guard with string match

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val result = match s:
    case "hello" if s.len() > 3: "long_hello"
    case "hello": "hello"
    case _: "other"
expect(result).to_equal("long_hello")
```

</details>

#### guard with equality check

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42
val result = match n:
    case 42 if n == 42: "perfect"
    case 42: "forty_two"
    case _: "other"
expect(result).to_equal("perfect")
```

</details>

### guard with multiple arms

#### multiple guards evaluated in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 7
val result = match x:
    case 7 if x > 10: "large"
    case 7 if x > 5: "medium"
    case 7: "small"
    case _: "other"
expect(result).to_equal("medium")
```

</details>

#### wildcard with guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
val result = match x:
    case 5: "five"
    case _ if x > 50: "large"
    case _: "other"
expect(result).to_equal("large")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/guard_clause_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- guard clauses
- basic guard evaluation
- guard with multiple arms

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
