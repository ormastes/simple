# Nn Extended Specification

> <details>

<!-- sdn-diagram:id=nn_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nn_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nn_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nn_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nn Extended Specification

## Scenarios

### Nn Extended

#### keeps convolution, pooling, normalization, and dropout layers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("class Conv2d:")
expect(source).to_contain("class MaxPool2d:")
expect(source).to_contain("class BatchNorm2d:")
expect(source).to_contain("class Dropout:")
```

</details>

#### keeps training and eval mode controls for dropout available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("static fn create(p: i64) -> Dropout")
expect(source).to_contain("fn forward(x: Tensor) -> Tensor")
expect(source).to_contain("me train():")
expect(source).to_contain("me eval():")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Nn Extended

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
