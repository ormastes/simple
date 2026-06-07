# Empty Array Map Lambda Specification

> <details>

<!-- sdn-diagram:id=empty_array_map_lambda_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=empty_array_map_lambda_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

empty_array_map_lambda_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=empty_array_map_lambda_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Empty Array Map Lambda Specification

## Scenarios

### empty array map lambda

#### maps wildcard lambda over empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([].map(\_: 0)).to_equal([])
```

</details>

#### maps named lambda over empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([].map(\f: f)).to_equal([])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/empty_array_map_lambda_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- empty array map lambda

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
