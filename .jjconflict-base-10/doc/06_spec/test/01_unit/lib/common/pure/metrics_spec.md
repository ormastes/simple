# Metrics Specification

> <details>

<!-- sdn-diagram:id=metrics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=metrics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

metrics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=metrics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metrics Specification

## Scenarios

### Metrics

#### keeps differentiable loss helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn cross_entropy_loss_tensor(logits: i64, targets: i64) -> i64")
expect(source).to_contain("fn compute_mse_loss_tensor(pred: i64, target: i64) -> i64")
expect(source).to_contain("rt_torch_torchtensor_log_softmax(logits, 1)")
expect(source).to_contain("rt_torch_torchtensor_mean_dim(per_sample, 0, false)")
```

</details>

#### keeps accuracy and learning-rate metric helpers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = torch_ops_source()

expect(source).to_contain("fn compute_accuracy(logits: i64, targets: i64) -> f64")
expect(source).to_contain("fn lr_warmup_linear(step: i64, warmup_steps: i64, total_steps: i64, base_lr: f64) -> f64")
expect(source).to_contain("fn lr_warmup_cosine(step: i64, warmup_steps: i64, total_steps: i64, base_lr: f64, min_lr: f64) -> f64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/pure/metrics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Metrics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
