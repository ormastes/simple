# Functional Specification

> <details>

<!-- sdn-diagram:id=functional_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=functional_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

functional_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=functional_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Functional Specification

## Scenarios

### Functional

#### keeps activation functions available on tensor wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_mod_source()

expect(source).to_contain("fn relu() -> Tensor")
expect(source).to_contain("fn sigmoid() -> Tensor")
expect(source).to_contain("fn tanh() -> Tensor")
expect(source).to_contain("fn softmax(dim: i64) -> Tensor")
expect(source).to_contain("fn log_softmax(dim: i64) -> Tensor")
```

</details>

#### keeps composed functional losses and metrics available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn cross_entropy_loss_tensor(logits: i64, targets: i64) -> i64")
expect(source).to_contain("fn compute_mse_loss_tensor(pred: i64, target: i64) -> i64")
expect(source).to_contain("fn compute_accuracy(logits: i64, targets: i64) -> f64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/nn/functional_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Functional

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
