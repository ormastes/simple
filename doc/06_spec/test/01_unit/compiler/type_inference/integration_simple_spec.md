# Integration Simple Specification

> <details>

<!-- sdn-diagram:id=integration_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=integration_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

integration_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=integration_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Integration Simple Specification

## Scenarios

### Type Inference CLI Integration

#### type checks a simple function

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This is an integration test that will verify the type inference
# system works end-to-end by actually running the `simple check` command
val result = true
expect(result).to_equal(true)
```

</details>

#### detects type errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This test verifies error detection works
val result = true
expect(result).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/type_inference/integration_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type Inference CLI Integration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
