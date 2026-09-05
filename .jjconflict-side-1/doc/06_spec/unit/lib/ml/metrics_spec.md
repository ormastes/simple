# Metrics Specification

> Tests covering ML Engine Metrics, Accuracy metric, Loss metric, MSE metric, MAE metric, RMSE metric, Metric base class.

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

- computes accuracy for perfect predictions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes accuracy for perfect predictions")
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [0, 1, 2], "labels": [0, 1, 2]})
expect acc.compute() == 1.0
```

</details>

#### computes accuracy for partial matches

- computes accuracy for partial matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes accuracy for partial matches")
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

- computes accuracy for all wrong predictions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes accuracy for all wrong predictions")
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [1, 2, 3], "labels": [0, 0, 0]})
expect acc.compute() == 0.0
```

</details>

#### accumulates across multiple batches

- accumulates across multiple batches


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accumulates across multiple batches")
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [0, 1], "labels": [0, 1]})  # 2 correct
acc.update({"pred": [0, 1], "labels": [1, 0]})  # 0 correct
# Total: 2 correct out of 4 = 0.5
expect acc.compute() == 0.5
```

</details>

#### handles empty output gracefully

- handles empty output gracefully


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty output gracefully")
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"pred": [], "labels": []})
expect acc.compute() == 0.0
```

</details>

#### supports y_pred/y_true format

- supports y_pred/y_true format


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports y_pred/y_true format")
var acc = Accuracy(correct: 0.0, total: 0.0)
acc.reset()
acc.update({"y_pred": [0, 1, 2], "y_true": [0, 1, 2]})
expect acc.compute() == 1.0
```

</details>

#### resets properly between epochs

- resets properly between epochs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets properly between epochs")
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

- computes average loss


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes average loss")
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
loss.update({"loss": 1.0})
loss.update({"loss": 2.0})
loss.update({"loss": 3.0})
expect loss.compute() == 2.0
```

</details>

#### handles single batch

- handles single batch


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single batch")
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
loss.update({"loss": 0.5})
expect loss.compute() == 0.5
```

</details>

#### handles empty updates

- handles empty updates


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty updates")
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
expect loss.compute() == 0.0
```

</details>

#### ignores output without loss key

- ignores output without loss key


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ignores output without loss key")
var loss = Loss(total_loss: 0.0, count: 0.0)
loss.reset()
loss.update({"other": 1.0})
expect loss.compute() == 0.0
```

</details>

#### resets properly between epochs

- resets properly between epochs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resets properly between epochs")
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

- computes MSE for perfect predictions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes MSE for perfect predictions")
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
mse.update({"pred": [1.0, 2.0, 3.0], "actual": [1.0, 2.0, 3.0]})
expect mse.compute() == 0.0
```

</details>

#### computes MSE for predictions with errors

- computes MSE for predictions with errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes MSE for predictions with errors")
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
# Errors: 1, 1 -> Squared: 1, 1 -> Mean: 1.0
mse.update({"pred": [2.0, 3.0], "actual": [1.0, 2.0]})
expect mse.compute() == 1.0
```

</details>

#### penalizes large errors more

- penalizes large errors more


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("penalizes large errors more")
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
# Error of 2 -> Squared: 4
mse.update({"pred": [3.0], "actual": [1.0]})
expect mse.compute() == 4.0
```

</details>

#### handles y_pred/y_true format

- handles y_pred/y_true format


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles y_pred/y_true format")
var mse = MSE(sum_sq: 0.0, count: 0.0)
mse.reset()
mse.update({"y_pred": [1.0], "y_true": [1.0]})
expect mse.compute() == 0.0
```

</details>

### MAE metric

#### computes MAE for perfect predictions

- computes MAE for perfect predictions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes MAE for perfect predictions")
var mae = MAE(sum_abs: 0.0, count: 0.0)
mae.reset()
mae.update({"pred": [1.0, 2.0, 3.0], "actual": [1.0, 2.0, 3.0]})
expect mae.compute() == 0.0
```

</details>

#### computes MAE for predictions with errors

- computes MAE for predictions with errors


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes MAE for predictions with errors")
var mae = MAE(sum_abs: 0.0, count: 0.0)
mae.reset()
# Errors: |2-1| + |3-2| = 1 + 1 = 2 -> Mean: 1.0
mae.update({"pred": [2.0, 3.0], "actual": [1.0, 2.0]})
expect mae.compute() == 1.0
```

</details>

#### handles negative errors correctly

- handles negative errors correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles negative errors correctly")
var mae = MAE(sum_abs: 0.0, count: 0.0)
mae.reset()
# Error: |0-2| = 2
mae.update({"pred": [0.0], "actual": [2.0]})
expect mae.compute() == 2.0
```

</details>

### RMSE metric

#### computes RMSE for perfect predictions

- computes RMSE for perfect predictions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes RMSE for perfect predictions")
var rmse = RMSE(sum_sq: 0.0, count: 0.0)
rmse.reset()
rmse.update({"pred": [1.0, 2.0], "actual": [1.0, 2.0]})
expect rmse.compute() == 0.0
```

</details>

#### computes RMSE as square root of MSE

- computes RMSE as square root of MSE


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("computes RMSE as square root of MSE")
var rmse = RMSE(sum_sq: 0.0, count: 0.0)
rmse.reset()
# MSE = 4.0 -> RMSE = 2.0
rmse.update({"pred": [3.0], "actual": [1.0]})
expect rmse.compute() == 2.0
```

</details>

### Metric base class

#### provides default compute returning zero

- provides default compute returning zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides default compute returning zero")
val metric = Metric()
expect metric.compute() == 0.0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/ml/metrics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ML Engine Metrics, Accuracy metric, Loss metric, MSE metric, MAE metric, RMSE metric, Metric base class.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ab96e1bc46ec00f4d7f1574eaaaf656a52a89066a0da38cf2b8ee3f8ff968e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ab96e1bc46ec00f4d7f1574eaaaf656a52a89066a0da38cf2b8ee3f8ff968e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ab96e1bc46ec00f4d7f1574eaaaf656a52a89066a0da38cf2b8ee3f8ff968e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/ml/metrics_spec.spl
mirror: doc/06_spec/unit/lib/ml/metrics_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/ml/metrics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/ml/metrics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/ml/metrics_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes accuracy for perfect predictions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/metrics_spec.spl:190:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes accuracy for partial matches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/ml/metrics_spec.spl:201:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes accuracy for all wrong predictions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
