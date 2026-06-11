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
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Guard Clause Specification

## Scenarios

### guard clauses in match

#### guard filters match arm

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val result = match x:
    case 10 if x > 5: "big ten"
    case 10: "small ten"
    case _: "other"
expect(result).to_equal("big ten")
```

</details>

#### guard false skips arm falls through

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val result = match x:
    case 3 if x > 5: "big"
    case _: "small"
expect(result).to_equal("small")
```

</details>

#### guard with complex condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42
val threshold = 40
val result = match n:
    case 42 if n > threshold: "above threshold"
    case _: "below"
expect(result).to_equal("above threshold")
```

</details>

#### guard with else fallthrough

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 7
val result = match x:
    case 7 if x < 5: "small seven"
    case 7: "seven"
    case _: "other"
expect(result).to_equal("seven")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/guard_clause_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- guard clauses in match

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
