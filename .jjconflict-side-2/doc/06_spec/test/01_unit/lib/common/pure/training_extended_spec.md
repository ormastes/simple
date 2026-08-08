# Training Extended Specification

> <details>

<!-- sdn-diagram:id=training_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=training_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

training_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=training_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Training Extended Specification

## Scenarios

### Training Extended

#### keeps CUDA stream and sequential training components available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_training_source()

expect(source).to_contain("class Stream:")
expect(source).to_contain("static fn create(device_id: i64) -> Stream")
expect(source).to_contain("fn synchronize():")
expect(source).to_contain("fn query() -> bool")
expect(source).to_contain("class Sequential:")
```

</details>

#### keeps sequential layer composition and parameter collection available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_training_source()

expect(source).to_contain("me add_layer_linear(layer: Linear)")
expect(source).to_contain("me add_layer_conv2d(layer: Conv2d)")
expect(source).to_contain("while i < self.layers_linear.len():")
expect(source).to_contain("while j < self.layers_conv2d.len():")
expect(source).to_contain("fn parameters() -> [Tensor]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/training_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Training Extended

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
