# Nested String Split Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nested String Split Specification

## Scenarios

### nested string split dispatch

#### splits a temporary string receiver

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = " a,b ".trim().split(",")

expect(parts.len()).to_equal(2)
expect(parts[0]).to_equal("a")
expect(parts[1]).to_equal("b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/interpreter/nested_string_split_spec.spl` |
| Updated | 2026-07-18 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nested string split dispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
