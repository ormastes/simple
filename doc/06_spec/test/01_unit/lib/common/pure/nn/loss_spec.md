# Loss Specification

> <details>

<!-- sdn-diagram:id=loss_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=loss_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

loss_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=loss_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Loss Specification

## Scenarios

### Loss

#### keeps object-oriented MSE and cross-entropy losses available

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_training_source()

expect(source).to_contain("class MSELoss:")
expect(source).to_contain("static fn create() -> MSELoss")
expect(source).to_contain("class CrossEntropyLoss:")
expect(source).to_contain("static fn create() -> CrossEntropyLoss")
expect(source).to_contain("Tensor.from_handle(rt_torch_tensor_from_data([loss_val], [1]))")
```

</details>

#### keeps differentiable tensor loss functions available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn cross_entropy_loss_tensor(logits: i64, targets: i64) -> i64")
expect(source).to_contain("fn compute_mse_loss_tensor(pred: i64, target: i64) -> i64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn/loss_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Loss

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
