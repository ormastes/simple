# Tensor Specification

> <details>

<!-- sdn-diagram:id=tensor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tensor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tensor_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tensor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Specification

## Scenarios

### std.ml.torch tensor smoke

#### creates a tensor and exposes shape metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tensor = torch.tensor([1.0, 2.0, 3.0])
expect(tensor.shape()).to_equal([3])
expect(tensor.numel()).to_equal(3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/stdlib/math/tensor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- std.ml.torch tensor smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
