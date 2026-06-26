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

#### defines scalar regression metrics with empty-input handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_metrics_source()

expect(src).to_contain("pub fn ml_mse_metric(y_true: [f64], y_pred: [f64]) -> f64:")
expect(src).to_contain("pub fn ml_mae_metric(y_true: [f64], y_pred: [f64]) -> f64:")
expect(src).to_contain("pub fn ml_r2(y_true: [f64], y_pred: [f64]) -> f64:")
expect(src).to_contain("pub fn ml_rmse(y_true: [f64], y_pred: [f64]) -> f64:")
expect(src).to_contain("if n == 0:")
expect(src).to_contain("return 0.0")
expect(src).to_contain("s / n.to_f64()")
expect(src).to_contain("rt_math_sqrt(ml_mse_metric(y_true, y_pred))")
```

</details>

<details>
<summary>Advanced: defines classification accuracy and binary confusion matrix metrics</summary>

#### defines classification accuracy and binary confusion matrix metrics

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = pure_metrics_source()

expect(src).to_contain("pub fn ml_accuracy_int(y_true: [int], y_pred: [int]) -> f64:")
expect(src).to_contain("pub fn ml_accuracy_float(y_true: [f64], y_pred: [f64]) -> f64:")
expect(src).to_contain("pub class ConfusionMatrix2:")
expect(src).to_contain("tp: int")
expect(src).to_contain("tn: int")
expect(src).to_contain("fp: int")
expect(src).to_contain("fn_count: int")
expect(src).to_contain("static fn compute(y_true: [int], y_pred: [int]) -> ConfusionMatrix2:")
expect(src).to_contain("fn precision() -> f64:")
expect(src).to_contain("fn recall() -> f64:")
expect(src).to_contain("fn f1() -> f64:")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/pure/metrics_spec.spl` |
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
