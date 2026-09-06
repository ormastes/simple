# ml_metrics_spec

> Tests pure evaluation metrics: MSE, MAE, R², RMSE, accuracy, and binary confusion matrix / precision / recall / F1.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ml_metrics_spec

Tests pure evaluation metrics: MSE, MAE, R², RMSE, accuracy, and binary confusion matrix / precision / recall / F1.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ml-metrics |
| Category | Stdlib / ML Consumer Layer |
| Difficulty | 2/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ml.md |
| Source | `test/feature/scilib/ml_metrics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests pure evaluation metrics: MSE, MAE, R², RMSE, accuracy, and
binary confusion matrix / precision / recall / F1.

Import path: use std.common.science_math.ml_metrics.{...}

## Scenarios

### ml_mse_metric

#### perfect prediction gives 0.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- perfect prediction gives 0.0
- perfect prediction gives 0.0
   - Expected: ml_mse_metric([1.0, 2.0, 3.0], [1.0, 2.0, 3.0]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perfect prediction gives 0.0")
step("perfect prediction gives 0.0")
# @req: REQ-FEAT-SCILIB-ML-METRICS-SPEC-001
expect(ml_mse_metric([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

- offset by 1 gives 1.0
- offset by 1 gives 1.0
   - Expected: ml_mse_metric([1.0, 2.0, 3.0], [2.0, 3.0, 4.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("offset by 1 gives 1.0")
step("offset by 1 gives 1.0")
# errors = [1,1,1], mse = 1.0
expect(ml_mse_metric([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### single element squared error

- single element squared error
- single element squared error
   - Expected: ml_mse_metric([3.0], [1.0]) equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("single element squared error")
step("single element squared error")
# (3-1)^2 = 4
expect(ml_mse_metric([3.0], [1.0])).to_equal(4.0)
```

</details>

#### empty inputs return 0.0

- empty inputs return 0.0
- empty inputs return 0.0
   - Expected: ml_mse_metric([], []) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty inputs return 0.0")
step("empty inputs return 0.0")
expect(ml_mse_metric([], [])).to_equal(0.0)
```

</details>

#### asymmetric errors

- asymmetric errors
- asymmetric errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("asymmetric errors")
step("asymmetric errors")
# errors^2 = [0, 4, 16], mean = 20/3
val result = ml_mse_metric([1.0, 2.0, 3.0], [1.0, 4.0, 7.0])
# 20/3 ≈ 6.666... — compare via to_be_greater_than
expect(result).to_be_greater_than(6.0)
expect(result).to_be_less_than(7.0)
```

</details>

### ml_mae_metric

#### perfect prediction gives 0.0

- perfect prediction gives 0.0
- perfect prediction gives 0.0
   - Expected: ml_mae_metric([1.0, 2.0, 3.0], [1.0, 2.0, 3.0]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perfect prediction gives 0.0")
step("perfect prediction gives 0.0")
expect(ml_mae_metric([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

- offset by 1 gives 1.0
- offset by 1 gives 1.0
   - Expected: ml_mae_metric([1.0, 2.0, 3.0], [2.0, 3.0, 4.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("offset by 1 gives 1.0")
step("offset by 1 gives 1.0")
expect(ml_mae_metric([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### absolute values — negative errors

- absolute values — negative errors
- absolute values — negative errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("absolute values — negative errors")
step("absolute values — negative errors")
# errors = |1-2|, |2-1|, |3-3| = 1, 1, 0 — mean = 2/3
val result = ml_mae_metric([1.0, 2.0, 3.0], [2.0, 1.0, 3.0])
expect(result).to_be_greater_than(0.6)
expect(result).to_be_less_than(0.7)
```

</details>

#### empty inputs return 0.0

- empty inputs return 0.0
- empty inputs return 0.0
   - Expected: ml_mae_metric([], []) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty inputs return 0.0")
step("empty inputs return 0.0")
expect(ml_mae_metric([], [])).to_equal(0.0)
```

</details>

### ml_r2

#### perfect prediction gives 1.0

- perfect prediction gives 1.0
- perfect prediction gives 1.0
   - Expected: ml_r2([1.0, 2.0, 3.0], [1.0, 2.0, 3.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perfect prediction gives 1.0")
step("perfect prediction gives 1.0")
expect(ml_r2([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(1.0)
```

</details>

#### mean prediction gives 0.0

- mean prediction gives 0.0
- mean prediction gives 0.0
   - Expected: ml_r2([1.0, 2.0, 3.0], [2.0, 2.0, 2.0]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mean prediction gives 0.0")
step("mean prediction gives 0.0")
# predicting mean(y_true) = 2.0 for all → R² = 0
expect(ml_r2([1.0, 2.0, 3.0], [2.0, 2.0, 2.0])).to_equal(0.0)
```

</details>

#### worse than mean gives negative R²

- worse than mean gives negative R²
- worse than mean gives negative R²


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("worse than mean gives negative R²")
step("worse than mean gives negative R²")
# large errors → ss_res > ss_tot
val result = ml_r2([1.0, 2.0, 3.0], [3.0, 2.0, 1.0])
expect(result).to_be_less_than(0.0)
```

</details>

#### near-perfect gives R² close to 1

- near-perfect gives R² close to 1
- near-perfect gives R² close to 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("near-perfect gives R² close to 1")
step("near-perfect gives R² close to 1")
# small errors
val result = ml_r2([1.0, 2.0, 3.0, 4.0, 5.0],
                   [1.1, 2.0, 3.1, 4.0, 4.9])
expect(result).to_be_greater_than(0.99)
```

</details>

#### empty inputs return 0.0

- empty inputs return 0.0
- empty inputs return 0.0
   - Expected: ml_r2([], []) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty inputs return 0.0")
step("empty inputs return 0.0")
expect(ml_r2([], [])).to_equal(0.0)
```

</details>

#### constant y_true perfect prediction returns 1.0

- constant y_true perfect prediction returns 1.0
- constant y_true perfect prediction returns 1.0
   - Expected: ml_r2([5.0, 5.0, 5.0], [5.0, 5.0, 5.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("constant y_true perfect prediction returns 1.0")
step("constant y_true perfect prediction returns 1.0")
# ss_tot = 0, ss_res = 0 → 1.0
expect(ml_r2([5.0, 5.0, 5.0], [5.0, 5.0, 5.0])).to_equal(1.0)
```

</details>

#### constant y_true imperfect prediction returns 0.0

- constant y_true imperfect prediction returns 0.0
- constant y_true imperfect prediction returns 0.0
   - Expected: ml_r2([5.0, 5.0, 5.0], [5.0, 5.0, 6.0]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("constant y_true imperfect prediction returns 0.0")
step("constant y_true imperfect prediction returns 0.0")
# ss_tot = 0, ss_res > 0 → 0.0
expect(ml_r2([5.0, 5.0, 5.0], [5.0, 5.0, 6.0])).to_equal(0.0)
```

</details>

### ml_rmse

#### perfect prediction gives 0.0

- perfect prediction gives 0.0
- perfect prediction gives 0.0
   - Expected: ml_rmse([1.0, 2.0, 3.0], [1.0, 2.0, 3.0]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perfect prediction gives 0.0")
step("perfect prediction gives 0.0")
expect(ml_rmse([1.0, 2.0, 3.0], [1.0, 2.0, 3.0])).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

- offset by 1 gives 1.0
- offset by 1 gives 1.0
   - Expected: ml_rmse([1.0, 2.0, 3.0], [2.0, 3.0, 4.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("offset by 1 gives 1.0")
step("offset by 1 gives 1.0")
# mse = 1.0, rmse = sqrt(1.0) = 1.0
expect(ml_rmse([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### rmse >= mae (Cauchy-Schwarz)

- rmse >= mae (Cauchy-Schwarz)
- rmse >= mae (Cauchy-Schwarz)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rmse >= mae (Cauchy-Schwarz)")
step("rmse >= mae (Cauchy-Schwarz)")
val y_t = [1.0, 3.0, 5.0, 7.0]
val y_p = [2.0, 2.0, 6.0, 6.0]
val rmse_val = ml_rmse(y_t, y_p)
val mae_val = ml_mae_metric(y_t, y_p)
expect(rmse_val).to_be_greater_than(mae_val - 0.001)
```

</details>

### ml_accuracy_int

#### all correct gives 1.0

- all correct gives 1.0
- all correct gives 1.0
   - Expected: ml_accuracy_int([0, 1, 2], [0, 1, 2]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all correct gives 1.0")
step("all correct gives 1.0")
expect(ml_accuracy_int([0, 1, 2], [0, 1, 2])).to_equal(1.0)
```

</details>

#### none correct gives 0.0

- none correct gives 0.0
- none correct gives 0.0
   - Expected: ml_accuracy_int([0, 0, 0], [1, 1, 1]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("none correct gives 0.0")
step("none correct gives 0.0")
expect(ml_accuracy_int([0, 0, 0], [1, 1, 1])).to_equal(0.0)
```

</details>

#### 3 out of 4 correct gives 0.75

- 3 out of 4 correct gives 0.75
- 3 out of 4 correct gives 0.75
   - Expected: ml_accuracy_int([0, 1, 1, 0], [0, 1, 0, 0]) equals `0.75`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("3 out of 4 correct gives 0.75")
step("3 out of 4 correct gives 0.75")
expect(ml_accuracy_int([0, 1, 1, 0], [0, 1, 0, 0])).to_equal(0.75)
```

</details>

#### empty returns 0.0

- empty returns 0.0
- empty returns 0.0
   - Expected: ml_accuracy_int([], []) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty returns 0.0")
step("empty returns 0.0")
expect(ml_accuracy_int([], [])).to_equal(0.0)
```

</details>

#### single correct

- single correct
- single correct
   - Expected: ml_accuracy_int([1], [1]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("single correct")
step("single correct")
expect(ml_accuracy_int([1], [1])).to_equal(1.0)
```

</details>

#### single incorrect

- single incorrect
- single incorrect
   - Expected: ml_accuracy_int([1], [0]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("single incorrect")
step("single incorrect")
expect(ml_accuracy_int([1], [0])).to_equal(0.0)
```

</details>

### ml_accuracy_float

#### all correct gives 1.0

- all correct gives 1.0
- all correct gives 1.0
   - Expected: ml_accuracy_float([0.0, 1.0, 0.0], [0.0, 1.0, 0.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all correct gives 1.0")
step("all correct gives 1.0")
expect(ml_accuracy_float([0.0, 1.0, 0.0], [0.0, 1.0, 0.0])).to_equal(1.0)
```

</details>

#### none correct gives 0.0

- none correct gives 0.0
- none correct gives 0.0
   - Expected: ml_accuracy_float([0.0, 0.0], [1.0, 1.0]) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("none correct gives 0.0")
step("none correct gives 0.0")
expect(ml_accuracy_float([0.0, 0.0], [1.0, 1.0])).to_equal(0.0)
```

</details>

#### half correct gives 0.5

- half correct gives 0.5
- half correct gives 0.5
   - Expected: ml_accuracy_float([0.0, 1.0], [1.0, 1.0]) equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("half correct gives 0.5")
step("half correct gives 0.5")
expect(ml_accuracy_float([0.0, 1.0], [1.0, 1.0])).to_equal(0.5)
```

</details>

#### empty returns 0.0

- empty returns 0.0
- empty returns 0.0
   - Expected: ml_accuracy_float([], []) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty returns 0.0")
step("empty returns 0.0")
expect(ml_accuracy_float([], [])).to_equal(0.0)
```

</details>

### ConfusionMatrix2 — compute

#### all TP — perfect positive classifier

- all TP — perfect positive classifier
- all TP — perfect positive classifier
   - Expected: cm.tp equals `3`
   - Expected: cm.tn equals `0`
   - Expected: cm.fp equals `0`
   - Expected: cm.fn_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all TP — perfect positive classifier")
step("all TP — perfect positive classifier")
val cm = ConfusionMatrix2.compute([1, 1, 1], [1, 1, 1])
expect(cm.tp).to_equal(3)
expect(cm.tn).to_equal(0)
expect(cm.fp).to_equal(0)
expect(cm.fn_count).to_equal(0)
```

</details>

#### all TN — perfect negative classifier

- all TN — perfect negative classifier
- all TN — perfect negative classifier
   - Expected: cm.tp equals `0`
   - Expected: cm.tn equals `3`
   - Expected: cm.fp equals `0`
   - Expected: cm.fn_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all TN — perfect negative classifier")
step("all TN — perfect negative classifier")
val cm = ConfusionMatrix2.compute([0, 0, 0], [0, 0, 0])
expect(cm.tp).to_equal(0)
expect(cm.tn).to_equal(3)
expect(cm.fp).to_equal(0)
expect(cm.fn_count).to_equal(0)
```

</details>

#### mixed — 2TP 1TN 1FP 1FN

- mixed — 2TP 1TN 1FP 1FN
- mixed — 2TP 1TN 1FP 1FN
   - Expected: cm.tp equals `2`
   - Expected: cm.tn equals `1`
   - Expected: cm.fp equals `1`
   - Expected: cm.fn_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("mixed — 2TP 1TN 1FP 1FN")
step("mixed — 2TP 1TN 1FP 1FN")
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

- all FP
- all FP
   - Expected: cm.fp equals `2`
   - Expected: cm.tp equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all FP")
step("all FP")
val cm = ConfusionMatrix2.compute([0, 0], [1, 1])
expect(cm.fp).to_equal(2)
expect(cm.tp).to_equal(0)
```

</details>

#### all FN

- all FN
- all FN
   - Expected: cm.fn_count equals `2`
   - Expected: cm.tp equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("all FN")
step("all FN")
val cm = ConfusionMatrix2.compute([1, 1], [0, 0])
expect(cm.fn_count).to_equal(2)
expect(cm.tp).to_equal(0)
```

</details>

### ConfusionMatrix2 — precision recall f1

#### perfect precision

- perfect precision
- perfect precision
   - Expected: cm.precision() equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perfect precision")
step("perfect precision")
# TP=3, FP=0 → precision=1.0
val cm = ConfusionMatrix2.compute([1, 1, 1], [1, 1, 1])
expect(cm.precision()).to_equal(1.0)
```

</details>

#### zero precision when all FP

- zero precision when all FP
- zero precision when all FP
   - Expected: cm.precision() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("zero precision when all FP")
step("zero precision when all FP")
# TP=0, FP=2
val cm = ConfusionMatrix2.compute([0, 0], [1, 1])
expect(cm.precision()).to_equal(0.0)
```

</details>

#### perfect recall

- perfect recall
- perfect recall
   - Expected: cm.recall() equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perfect recall")
step("perfect recall")
val cm = ConfusionMatrix2.compute([1, 1, 1], [1, 1, 1])
expect(cm.recall()).to_equal(1.0)
```

</details>

#### zero recall when all FN

- zero recall when all FN
- zero recall when all FN
   - Expected: cm.recall() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("zero recall when all FN")
step("zero recall when all FN")
val cm = ConfusionMatrix2.compute([1, 1], [0, 0])
expect(cm.recall()).to_equal(0.0)
```

</details>

#### F1 is harmonic mean of precision and recall

- F1 is harmonic mean of precision and recall
- F1 is harmonic mean of precision and recall


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("F1 is harmonic mean of precision and recall")
step("F1 is harmonic mean of precision and recall")
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

- F1 is 1.0 for perfect classifier
- F1 is 1.0 for perfect classifier
   - Expected: cm.f1() equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("F1 is 1.0 for perfect classifier")
step("F1 is 1.0 for perfect classifier")
val cm = ConfusionMatrix2.compute([1, 1, 0, 0], [1, 1, 0, 0])
expect(cm.f1()).to_equal(1.0)
```

</details>

#### F1 is 0.0 when no TP

- F1 is 0.0 when no TP
- F1 is 0.0 when no TP
   - Expected: cm.f1() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("F1 is 0.0 when no TP")
step("F1 is 0.0 when no TP")
val cm = ConfusionMatrix2.compute([1, 1], [0, 0])
expect(cm.f1()).to_equal(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_ml.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-SCILIB-ML-METRICS-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d805511894c687c2d5a1c148f703c14a71b47bb2f9297744508e0e56e43b1566`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d805511894c687c2d5a1c148f703c14a71b47bb2f9297744508e0e56e43b1566`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d805511894c687c2d5a1c148f703c14a71b47bb2f9297744508e0e56e43b1566`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/ml_metrics_spec.spl
mirror: doc/06_spec/feature/scilib/ml_metrics_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ml_metrics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ml_metrics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ml_metrics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 46 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/ml_metrics_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'perfect prediction gives 0.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ml_metrics_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'offset by 1 gives 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ml_metrics_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single element squared error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
