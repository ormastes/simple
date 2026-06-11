# Autograd Specification

> <details>

<!-- sdn-diagram:id=autograd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=autograd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

autograd_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=autograd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Autograd Specification

## Scenarios

### Autograd

#### gradient tracking

#### tracks gradients

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### backward pass

#### computes backward pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### gradient operations

#### accumulates gradients

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip
```

</details>

#### gradient checkpointing

#### supports gradient checkpointing

1. expect checkpoint supports checkpointing
2. expect checkpoint checkpoint segment


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checkpoint = MockGradientCheckpoint()
expect checkpoint.supports_checkpointing()
expect checkpoint.checkpoint_segment(start: 0, end: 100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/ml/autograd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Autograd

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
