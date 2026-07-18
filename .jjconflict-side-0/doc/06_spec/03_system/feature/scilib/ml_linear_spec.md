# Ml Linear Specification

> <details>

<!-- sdn-diagram:id=ml_linear_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ml_linear_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ml_linear_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ml_linear_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ml Linear Specification

## Scenarios

### LinearRegression — construction

#### new model is not fitted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = LinearRegression.new()
expect(m.is_fitted()).to_equal(false)
```

</details>

#### new model has empty coef

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = LinearRegression.new()
expect(m.coef().len()).to_equal(0)
```

</details>

#### new model has zero intercept

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val m = LinearRegression.new()
expect(m.intercept()).to_equal(0.0)
```

</details>

### LinearRegression — set_coef

#### is_fitted becomes true after set_coef

1. var m = LinearRegression new
2. m set coef
   - Expected: m.is_fitted() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.is_fitted()).to_equal(true)
```

</details>

#### coef returns injected value

1. var m = LinearRegression new
2. m set coef
   - Expected: c.len() equals `2`
   - Expected: c[0] equals `3.5`
   - Expected: c[1] equals `-1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = LinearRegression.new()
m.set_coef([3.5, -1.0], 0.5)
val c = m.coef()
expect(c.len()).to_equal(2)
expect(c[0]).to_equal(3.5)
expect(c[1]).to_equal(-1.0)
```

</details>

#### intercept returns injected value

1. var m = LinearRegression new
2. m set coef
   - Expected: m.intercept() equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.intercept()).to_equal(1.0)
```

</details>

### LinearRegression — predict

#### predicts correct value for x=0

1. var m = LinearRegression new
2. m set coef
   - Expected: m.predict([0.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# y = 2*0 + 1 = 1
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([0.0])).to_equal(1.0)
```

</details>

#### predicts correct value for x=1

1. var m = LinearRegression new
2. m set coef
   - Expected: m.predict([1.0]) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# y = 2*1 + 1 = 3
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([1.0])).to_equal(3.0)
```

</details>

#### predicts correct value for x=5

1. var m = LinearRegression new
2. m set coef
   - Expected: m.predict([5.0]) equals `11.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# y = 2*5 + 1 = 11
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([5.0])).to_equal(11.0)
```

</details>

#### predicts negative value

1. var m = LinearRegression new
2. m set coef
   - Expected: m.predict([-3.0]) equals `-5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# y = 2*(-3) + 1 = -5
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([-3.0])).to_equal(-5.0)
```

</details>

#### predicts with two features

1. var m = LinearRegression new
2. m set coef
   - Expected: m.predict([3.0, 4.0]) equals `11.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# y = 1*x0 + 2*x1 + 0 = 1*3 + 2*4 = 11
var m = LinearRegression.new()
m.set_coef([1.0, 2.0], 0.0)
expect(m.predict([3.0, 4.0])).to_equal(11.0)
```

</details>

### LinearRegression — predict_batch

#### returns correct length

1. var m = LinearRegression new
2. m set coef
   - Expected: preds.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
val preds = m.predict_batch([[0.0], [1.0], [2.0]])
expect(preds.len()).to_equal(3)
```

</details>

#### batch matches individual predictions

1. var m = LinearRegression new
2. m set coef
   - Expected: preds[0] equals `1.0`
   - Expected: preds[1] equals `3.0`
   - Expected: preds[2] equals `11.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
val preds = m.predict_batch([[0.0], [1.0], [5.0]])
expect(preds[0]).to_equal(1.0)
expect(preds[1]).to_equal(3.0)
expect(preds[2]).to_equal(11.0)
```

</details>

#### empty batch returns empty

1. var m = LinearRegression new
2. m set coef
   - Expected: preds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
val preds = m.predict_batch([])
expect(preds.len()).to_equal(0)
```

</details>

### Ridge — construction

#### new model is not fitted

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ridge.new(1.0)
expect(r.is_fitted()).to_equal(false)
```

</details>

#### alpha is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ridge.new(0.5)
expect(r.alpha()).to_equal(0.5)
```

</details>

#### alpha zero is valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ridge.new(0.0)
expect(r.alpha()).to_equal(0.0)
```

</details>

### Ridge — set_coef and predict

#### is_fitted becomes true after set_coef

1. var r = Ridge new
2. r set coef
   - Expected: r.is_fitted() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ridge.new(1.0)
r.set_coef([1.5], 0.0)
expect(r.is_fitted()).to_equal(true)
```

</details>

#### predict matches injected coef

1. var r = Ridge new
2. r set coef
   - Expected: r.predict([2.0]) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# y = 1.5*2 + 0 = 3.0
var r = Ridge.new(1.0)
r.set_coef([1.5], 0.0)
expect(r.predict([2.0])).to_equal(3.0)
```

</details>

#### Ridge alpha=0 behaves like LinearRegression

1. var lr = LinearRegression new
2. lr set coef
3. var ridge = Ridge new
4. ridge set coef
   - Expected: lr.predict([3.0]) equals `ridge.predict([3.0])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# With same coefficients, prediction is identical
var lr = LinearRegression.new()
lr.set_coef([2.0], 1.0)
var ridge = Ridge.new(0.0)
ridge.set_coef([2.0], 1.0)
expect(lr.predict([3.0])).to_equal(ridge.predict([3.0]))
```

</details>

#### intercept is preserved

1. var r = Ridge new
2. r set coef
   - Expected: r.predict([99.0]) equals `7.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = Ridge.new(10.0)
r.set_coef([0.0], 7.5)
expect(r.predict([99.0])).to_equal(7.5)
```

</details>

### ml_predict_linear

#### computes dot product plus intercept

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 2*3 + 0.5 = 6.5
expect(ml_predict_linear([2.0], 0.5, [3.0])).to_equal(6.5)
```

</details>

#### handles two features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 1*2 + 3*4 + 1 = 15
expect(ml_predict_linear([1.0, 3.0], 1.0, [2.0, 4.0])).to_equal(15.0)
```

</details>

#### zero intercept

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_predict_linear([5.0], 0.0, [2.0])).to_equal(10.0)
```

</details>

#### negative coefficient

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# -1*4 + 0 = -4
expect(ml_predict_linear([-1.0], 0.0, [4.0])).to_equal(-4.0)
```

</details>

### ml_mse

#### perfect prediction gives 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = [1.0, 2.0, 3.0]
expect(ml_mse(y, y)).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mse([1,2,3], [2,3,4]) = mean([1,1,1]) = 1.0
expect(ml_mse([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### single element

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_mse([3.0], [1.0])).to_equal(4.0)
```

</details>

#### empty returns 0.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ml_mse([], [])).to_equal(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/ml_linear_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LinearRegression — construction
- LinearRegression — set_coef
- LinearRegression — predict
- LinearRegression — predict_batch
- Ridge — construction
- Ridge — set_coef and predict
- ml_predict_linear
- ml_mse

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
