# Metrics Specification

> 1. var acc = Accuracy

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
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Metrics Specification

## Scenarios

### ML Engine Metrics

### Accuracy metric

#### computes accuracy for perfect predictions

1. var acc = Accuracy
2. acc reset
3. acc update
4. expect acc compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [0, 1, 2], "labels": [0, 1, 2]})
expect acc.compute() == 1.0
```

</details>

#### computes accuracy for partial matches

1. var acc = Accuracy
2. acc reset
3. acc update


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [0, 1, 0], "labels": [0, 0, 0]})
# 2 correct out of 3: 0.666...
val result = acc.compute()
expect result > 0.66
expect result < 0.67
```

</details>

#### computes accuracy for all wrong predictions

1. var acc = Accuracy
2. acc reset
3. acc update
4. expect acc compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [1, 2, 3], "labels": [0, 0, 0]})
expect acc.compute() == 0.0
```

</details>

#### accumulates across multiple batches

1. var acc = Accuracy
2. acc reset
3. acc update
4. acc update
5. expect acc compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [0, 1], "labels": [0, 1]})  # 2 correct
acc.update({"pred": [0, 1], "labels": [1, 0]})  # 0 correct
# Total: 2 correct out of 4 = 0.5
expect acc.compute() == 0.5
```

</details>

#### handles empty output gracefully

1. var acc = Accuracy
2. acc reset
3. acc update
4. expect acc compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [], "labels": []})
expect acc.compute() == 0.0
```

</details>

#### supports y_pred/y_true format

1. var acc = Accuracy
2. acc reset
3. acc update
4. expect acc compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"y_pred": [0, 1, 2], "y_true": [0, 1, 2]})
expect acc.compute() == 1.0
```

</details>

#### resets properly between epochs

1. var acc = Accuracy
2. acc reset
3. acc update
4. expect acc compute
5. acc reset
6. acc update
7. expect acc compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [0], "labels": [0]})
expect acc.compute() == 1.0

acc.reset()
acc.update({"pred": [0], "labels": [1]})
expect acc.compute() == 0.0
```

</details>

### Loss metric

#### computes average loss

1. var loss = Loss
2. loss reset
3. loss update
4. loss update
5. loss update
6. expect loss compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
loss.update({"loss": 1.0})
loss.update({"loss": 2.0})
loss.update({"loss": 3.0})
expect loss.compute() == 2.0
```

</details>

#### handles single batch

1. var loss = Loss
2. loss reset
3. loss update
4. expect loss compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
loss.update({"loss": 0.5})
expect loss.compute() == 0.5
```

</details>

#### handles empty updates

1. var loss = Loss
2. loss reset
3. expect loss compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
expect loss.compute() == 0.0
```

</details>

#### ignores output without loss key

1. var loss = Loss
2. loss reset
3. loss update
4. expect loss compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
loss.update({"other": 1.0})
expect loss.compute() == 0.0
```

</details>

#### resets properly between epochs

1. var loss = Loss
2. loss reset
3. loss update
4. expect loss compute
5. loss reset
6. loss update
7. expect loss compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
loss.update({"loss": 10.0})
expect loss.compute() == 10.0

loss.reset()
loss.update({"loss": 1.0})
expect loss.compute() == 1.0
```

</details>

### MSE metric

#### computes MSE for perfect predictions

1. var mse = MSE
2. mse reset
3. mse update
4. expect mse compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
mse.update({"pred": [1.0, 2.0, 3.0], "actual": [1.0, 2.0, 3.0]})
expect mse.compute() == 0.0
```

</details>

#### computes MSE for predictions with errors

1. var mse = MSE
2. mse reset
3. mse update
4. expect mse compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
# Errors: 1, 1 -> Squared: 1, 1 -> Mean: 1.0
mse.update({"pred": [2.0, 3.0], "actual": [1.0, 2.0]})
expect mse.compute() == 1.0
```

</details>

#### penalizes large errors more

1. var mse = MSE
2. mse reset
3. mse update
4. expect mse compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
# Error of 2 -> Squared: 4
mse.update({"pred": [3.0], "actual": [1.0]})
expect mse.compute() == 4.0
```

</details>

#### handles y_pred/y_true format

1. var mse = MSE
2. mse reset
3. mse update
4. expect mse compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
mse.update({"y_pred": [1.0], "y_true": [1.0]})
expect mse.compute() == 0.0
```

</details>

### MAE metric

#### computes MAE for perfect predictions

1. var mae = MAE
2. mae reset
3. mae update
4. expect mae compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mae = MAE(sum_abs: 0.0, count: 0.0)
mae.reset()
mae.update({"pred": [1.0, 2.0, 3.0], "actual": [1.0, 2.0, 3.0]})
expect mae.compute() == 0.0
```

</details>

#### computes MAE for predictions with errors

1. var mae = MAE
2. mae reset
3. mae update
4. expect mae compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mae = MAE(sum_abs: 0.0, count: 0.0)
mae.reset()
# Errors: |2-1| + |3-2| = 1 + 1 = 2 -> Mean: 1.0
mae.update({"pred": [2.0, 3.0], "actual": [1.0, 2.0]})
expect mae.compute() == 1.0
```

</details>

#### handles negative errors correctly

1. var mae = MAE
2. mae reset
3. mae update
4. expect mae compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mae = MAE(sum_abs: 0.0, count: 0.0)
mae.reset()
# Error: |0-2| = 2
mae.update({"pred": [0.0], "actual": [2.0]})
expect mae.compute() == 2.0
```

</details>

### RMSE metric

#### computes RMSE for perfect predictions

1. var rmse = RMSE
2. rmse reset
3. rmse update
4. expect rmse compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rmse = RMSE(sum_sq: 0.0, count: 0.0)
rmse.reset()
rmse.update({"pred": [1.0, 2.0], "actual": [1.0, 2.0]})
expect rmse.compute() == 0.0
```

</details>

#### computes RMSE as square root of MSE

1. var rmse = RMSE
2. rmse reset
3. rmse update
4. expect rmse compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rmse = RMSE(sum_sq: 0.0, count: 0.0)
rmse.reset()
# MSE = 4.0 -> RMSE = 2.0
rmse.update({"pred": [3.0], "actual": [1.0]})
expect rmse.compute() == 2.0
```

</details>

### Metric base class

#### provides default compute returning zero

1. expect metric compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metric = Metric()
expect metric.compute() == 0.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/ml/metrics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ML Engine Metrics
- Accuracy metric
- Loss metric
- MSE metric
- MAE metric
- RMSE metric
- Metric base class

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
