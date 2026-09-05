# Nn Specification

> <details>

<!-- sdn-diagram:id=nn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=nn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

nn_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=nn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Nn Specification

## Scenarios

### Nn

#### keeps neural network layer wrappers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("class Linear:")
expect(source).to_contain("class Conv2d:")
expect(source).to_contain("class MaxPool2d:")
expect(source).to_contain("class BatchNorm2d:")
expect(source).to_contain("class Dropout:")
```

</details>

#### keeps layer forward and parameter methods available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("fn forward(x: Tensor) -> Tensor")
expect(source).to_contain("fn parameters() -> [Tensor]")
expect(source).to_contain("static fn create(in_features: i64, out_features: i64) -> Linear")
expect(source).to_contain("static fn create(num_features: i64) -> BatchNorm2d")
```

</details>

#### keeps sequential model composition available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_training_source()

expect(source).to_contain("class Sequential:")
expect(source).to_contain("me add_layer_linear(layer: Linear)")
expect(source).to_contain("me add_layer_conv2d(layer: Conv2d)")
expect(source).to_contain("fn forward(x: Tensor) -> Tensor")
expect(source).to_contain("fn parameters() -> [Tensor]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Nn

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
