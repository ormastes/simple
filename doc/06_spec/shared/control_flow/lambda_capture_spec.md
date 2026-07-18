# Lambda Capture Specification

> 1. expect f

<!-- sdn-diagram:id=lambda_capture_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lambda_capture_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lambda_capture_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lambda_capture_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lambda Capture Specification

## Scenarios

### lambda capture

#### captures parent locals

1. expect f


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seed = 5
val f = \: seed + 7
expect f() == 12
```

</details>

#### captures function parameters

1. fn make

2. f

3. expect make


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn make(seed: i64) -> i64:
    val f = \: seed + 7
    f()

expect make(5) == 12
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/shared/control_flow/lambda_capture_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lambda capture

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
