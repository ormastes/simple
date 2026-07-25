# Ml Metrics Specification

> <details>

<!-- sdn-diagram:id=ml_metrics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ml_metrics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ml_metrics_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ml_metrics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Metrics Specification

## Scenarios

### ml_mse_metric

#### perfect prediction gives 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_mse_metric([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# errors = [1,1,1], mse = 1.0
expect(ml_mse_metric([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### single element squared error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# (3-1)^2 = 4
expect(ml_mse_metric([3.0], [1.0])).to_equal(4.0)
```

</details>

#### empty inputs return 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_mse_metric([], [])).to_equal(0.0)
```

</details>

#### asymmetric errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# errors^2 = [0, 4, 16], mean = 20/3
val result = ml_mse_metric([1.0, 2.0, 3.0], [1.0, 4.0, 7.0])
# 20/3 ≈ 6.666... — compare via to_be_greater_than
expect(result).to_be_greater_than(6.0)
expect(result).to_be_less_than(7.0)
```

</details>

### ml_mae_metric

#### perfect prediction gives 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_mae_metric([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_mae_metric([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### absolute values — negative errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# errors = |1-2|, |2-1|, |3-3| = 1, 1, 0 — mean = 2/3
val result = ml_mae_metric([1.0, 2.0, 3.0], [2.0, 1.0, 3.0])
expect(result).to_be_greater_than(0.6)
expect(result).to_be_less_than(0.7)
```

</details>

#### empty inputs return 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_mae_metric([], [])).to_equal(0.0)
```

</details>

### ml_r2

#### perfect prediction gives 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_r2([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(1.0)
```

</details>

#### mean prediction gives 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# predicting mean(y_true) = 2.0 for all → R² = 0
expect(ml_r2([1.0, 2.0, 3.0], [2.0, 2.0, 2.0])).to_equal(0.0)
```

</details>

#### worse than mean gives negative R²

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# large errors → ss_res > ss_tot
val result = ml_r2([1.0, 2.0, 3.0], [3.0, 2.0, 1.0])
expect(result).to_be_less_than(0.0)
```

</details>

#### near-perfect gives R² close to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# small errors
val result = ml_r2([1.0, 2.0, 3.0, 4.0, 5.0],
                   [1.1, 2.0, 3.1, 4.0, 4.9])
expect(result).to_be_greater_than(0.99)
```

</details>

#### empty inputs return 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_r2([], [])).to_equal(0.0)
```

</details>

#### constant y_true perfect prediction returns 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ss_tot = 0, ss_res = 0 → 1.0
expect(ml_r2([5.0, 5.0, 5.0], [5.0, 5.0, 5.0])).to_equal(1.0)
```

</details>

#### constant y_true imperfect prediction returns 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ss_tot = 0, ss_res > 0 → 0.0
expect(ml_r2([5.0, 5.0, 5.0], [5.0, 5.0, 6.0])).to_equal(0.0)
```

</details>

### ml_rmse

#### perfect prediction gives 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_rmse([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mse = 1.0, rmse = sqrt(1.0) = 1.0
expect(ml_rmse([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### rmse >= mae (Cauchy-Schwarz)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y_t = [1.0, 3.0, 5.0, 7.0]
val y_p = [2.0, 2.0, 6.0, 6.0]
val rmse_val = ml_rmse(y_t, y_p)
val mae_val = ml_mae_metric(y_t, y_p)
expect(rmse_val).to_be_greater_than(mae_val - 0.001)
```

</details>

### ml_accuracy_int

#### all correct gives 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_int([0, 1, 2], [0, 1, 2])).to_equal(1.0)
```

</details>

#### none correct gives 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_int([0, 0, 0], [1, 1, 1])).to_equal(0.0)
```

</details>

#### 3 out of 4 correct gives 0.75

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_int([0, 1, 1, 0], [0, 1, 0, 0])).to_equal(0.75)
```

</details>

#### empty returns 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_int([], [])).to_equal(0.0)
```

</details>

#### single correct

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_int([1], [1])).to_equal(1.0)
```

</details>

#### single incorrect

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_int([1], [0])).to_equal(0.0)
```

</details>

### ml_accuracy_float

#### all correct gives 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_float([0.0, 1.0, 0.0], [0.0, 1.0, 0.0])).to_equal(1.0)
```

</details>

#### none correct gives 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_float([0.0, 0.0], [1.0, 1.0])).to_equal(0.0)
```

</details>

#### half correct gives 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_float([0.0, 1.0], [1.0, 1.0])).to_equal(0.5)
```

</details>

#### empty returns 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_accuracy_float([], [])).to_equal(0.0)
```

</details>

### ConfusionMatrix2 — compute

#### all TP — perfect positive classifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([1, 1, 1], [1, 1, 1])
expect(cm.tp).to_equal(3)
expect(cm.tn).to_equal(0)
expect(cm.fp).to_equal(0)
expect(cm.fn_count).to_equal(0)
```

</details>

#### all TN — perfect negative classifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([0, 0, 0], [0, 0, 0])
expect(cm.tp).to_equal(0)
expect(cm.tn).to_equal(3)
expect(cm.fp).to_equal(0)
expect(cm.fn_count).to_equal(0)
```

</details>

#### mixed — 2TP 1TN 1FP 1FN

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# true: 1 1 0 0 1  pred: 1 1 0 1 0
val y_t = [1, 1, 0, 0, 1]
val y_p = [1, 1, 0, 1, 0]
val cm = ConfusionMatrix2.compute(y_t, y_p)
expect(cm.tp).to_equal(2)
expect(cm.tn).to_equal(1)
expect(cm.fp).to_equal(1)
expect(cm.fn_count).to_equal(1)
```

</details>

#### all FP

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([0, 0], [1, 1])
expect(cm.fp).to_equal(2)
expect(cm.tp).to_equal(0)
```

</details>

#### all FN

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([1, 1], [0, 0])
expect(cm.fn_count).to_equal(2)
expect(cm.tp).to_equal(0)
```

</details>

### ConfusionMatrix2 — precision recall f1

#### perfect precision

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TP=3, FP=0 → precision=1.0
val cm = ConfusionMatrix2.compute([1, 1, 1], [1, 1, 1])
expect(cm.precision()).to_equal(1.0)
```

</details>

#### zero precision when all FP

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TP=0, FP=2
val cm = ConfusionMatrix2.compute([0, 0], [1, 1])
expect(cm.precision()).to_equal(0.0)
```

</details>

#### perfect recall

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([1, 1, 1], [1, 1, 1])
expect(cm.recall()).to_equal(1.0)
```

</details>

#### zero recall when all FN

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([1, 1], [0, 0])
expect(cm.recall()).to_equal(0.0)
```

</details>

#### F1 is harmonic mean of precision and recall

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# TP=2, FP=1, FN=1 → precision=2/3, recall=2/3 → F1=2/3
val y_t = [1, 1, 0, 0, 1, 1]
val y_p = [1, 1, 1, 0, 0, 1]
val cm = ConfusionMatrix2.compute(y_t, y_p)
val f = cm.f1()
expect(f).to_be_greater_than(0.6)
expect(f).to_be_less_than(0.8)
```

</details>

#### F1 is 1.0 for perfect classifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([1, 1, 0, 0], [1, 1, 0, 0])
expect(cm.f1()).to_equal(1.0)
```

</details>

#### F1 is 0.0 when no TP

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cm = ConfusionMatrix2.compute([1, 1], [0, 0])
expect(cm.f1()).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/ml_metrics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ml_mse_metric
- ml_mae_metric
- ml_r2
- ml_rmse
- ml_accuracy_int
- ml_accuracy_float
- ConfusionMatrix2 — compute
- ConfusionMatrix2 — precision recall f1

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
