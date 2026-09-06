# ml_linear_spec

> Tests the pure consumer layer for LinearRegression and Ridge. Coefficients are injected directly (simulating what linalg.solve would produce) — no solver is called here.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ml_linear_spec

Tests the pure consumer layer for LinearRegression and Ridge. Coefficients are injected directly (simulating what linalg.solve would produce) — no solver is called here.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-ml-linear |
| Category | Stdlib / ML Consumer Layer |
| Difficulty | 2/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_ml.md |
| Source | `test/feature/scilib/ml_linear_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the pure consumer layer for LinearRegression and Ridge.
Coefficients are injected directly (simulating what linalg.solve
would produce) — no solver is called here.

Import path: use std.common.science_math.ml_linear.{LinearRegression, Ridge, ml_predict_linear, ml_mse}

## Scenarios

### LinearRegression — construction

#### new model is not fitted

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new model is not fitted
- new model is not fitted
   - Expected: m.is_fitted() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("new model is not fitted")
step("new model is not fitted")
# @req: REQ-FEAT-SCILIB-ML-LINEAR-SPEC-001
val m = LinearRegression.new()
expect(m.is_fitted()).to_equal(false)
```

</details>

#### new model has empty coef

- new model has empty coef
- new model has empty coef
   - Expected: m.coef().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("new model has empty coef")
step("new model has empty coef")
val m = LinearRegression.new()
expect(m.coef().len()).to_equal(0)
```

</details>

#### new model has zero intercept

- new model has zero intercept
- new model has zero intercept
   - Expected: m.intercept() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("new model has zero intercept")
step("new model has zero intercept")
val m = LinearRegression.new()
expect(m.intercept()).to_equal(0.0)
```

</details>

### LinearRegression — set_coef

#### is_fitted becomes true after set_coef

- is_fitted becomes true after set_coef
- is_fitted becomes true after set_coef
   - Expected: m.is_fitted() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_fitted becomes true after set_coef")
step("is_fitted becomes true after set_coef")
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.is_fitted()).to_equal(true)
```

</details>

#### coef returns injected value

- coef returns injected value
- coef returns injected value
   - Expected: c.len() equals `2`
   - Expected: c[0] equals `3.5`
   - Expected: c[1] equals `-1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("coef returns injected value")
step("coef returns injected value")
var m = LinearRegression.new()
m.set_coef([3.5, -1.0], 0.5)
val c = m.coef()
expect(c.len()).to_equal(2)
expect(c[0]).to_equal(3.5)
expect(c[1]).to_equal(-1.0)
```

</details>

#### intercept returns injected value

- intercept returns injected value
- intercept returns injected value
   - Expected: m.intercept() equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("intercept returns injected value")
step("intercept returns injected value")
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.intercept()).to_equal(1.0)
```

</details>

### LinearRegression — predict

#### predicts correct value for x=0

- predicts correct value for x=0
- predicts correct value for x=0
   - Expected: m.predict([0.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("predicts correct value for x=0")
step("predicts correct value for x=0")
# y = 2*0 + 1 = 1
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([0.0])).to_equal(1.0)
```

</details>

#### predicts correct value for x=1

- predicts correct value for x=1
- predicts correct value for x=1
   - Expected: m.predict([1.0]) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("predicts correct value for x=1")
step("predicts correct value for x=1")
# y = 2*1 + 1 = 3
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([1.0])).to_equal(3.0)
```

</details>

#### predicts correct value for x=5

- predicts correct value for x=5
- predicts correct value for x=5
   - Expected: m.predict([5.0]) equals `11.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("predicts correct value for x=5")
step("predicts correct value for x=5")
# y = 2*5 + 1 = 11
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([5.0])).to_equal(11.0)
```

</details>

#### predicts negative value

- predicts negative value
- predicts negative value
   - Expected: m.predict([-3.0]) equals `-5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("predicts negative value")
step("predicts negative value")
# y = 2*(-3) + 1 = -5
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
expect(m.predict([-3.0])).to_equal(-5.0)
```

</details>

#### predicts with two features

- predicts with two features
- predicts with two features
   - Expected: m.predict([3.0, 4.0]) equals `11.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("predicts with two features")
step("predicts with two features")
# y = 1*x0 + 2*x1 + 0 = 1*3 + 2*4 = 11
var m = LinearRegression.new()
m.set_coef([1.0, 2.0], 0.0)
expect(m.predict([3.0, 4.0])).to_equal(11.0)
```

</details>

### LinearRegression — predict_batch

#### returns correct length

- returns correct length
- returns correct length
   - Expected: preds.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns correct length")
step("returns correct length")
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
val preds = m.predict_batch([[0.0], [1.0], [2.0]])
expect(preds.len()).to_equal(3)
```

</details>

#### batch matches individual predictions

- batch matches individual predictions
- batch matches individual predictions
   - Expected: preds[0] equals `1.0`
   - Expected: preds[1] equals `3.0`
   - Expected: preds[2] equals `11.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("batch matches individual predictions")
step("batch matches individual predictions")
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
val preds = m.predict_batch([[0.0], [1.0], [5.0]])
expect(preds[0]).to_equal(1.0)
expect(preds[1]).to_equal(3.0)
expect(preds[2]).to_equal(11.0)
```

</details>

#### empty batch returns empty

- empty batch returns empty
- empty batch returns empty
   - Expected: preds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty batch returns empty")
step("empty batch returns empty")
var m = LinearRegression.new()
m.set_coef([2.0], 1.0)
val preds = m.predict_batch([])
expect(preds.len()).to_equal(0)
```

</details>

### Ridge — construction

#### new model is not fitted

- new model is not fitted
- new model is not fitted
   - Expected: r.is_fitted() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("new model is not fitted")
step("new model is not fitted")
val r = Ridge.new(1.0)
expect(r.is_fitted()).to_equal(false)
```

</details>

#### alpha is stored

- alpha is stored
- alpha is stored
   - Expected: r.alpha() equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("alpha is stored")
step("alpha is stored")
val r = Ridge.new(0.5)
expect(r.alpha()).to_equal(0.5)
```

</details>

#### alpha zero is valid

- alpha zero is valid
- alpha zero is valid
   - Expected: r.alpha() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("alpha zero is valid")
step("alpha zero is valid")
val r = Ridge.new(0.0)
expect(r.alpha()).to_equal(0.0)
```

</details>

### Ridge — set_coef and predict

#### is_fitted becomes true after set_coef

- is_fitted becomes true after set_coef
- is_fitted becomes true after set_coef
   - Expected: r.is_fitted() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("is_fitted becomes true after set_coef")
step("is_fitted becomes true after set_coef")
var r = Ridge.new(1.0)
r.set_coef([1.5], 0.0)
expect(r.is_fitted()).to_equal(true)
```

</details>

#### predict matches injected coef

- predict matches injected coef
- predict matches injected coef
   - Expected: r.predict([2.0]) equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("predict matches injected coef")
step("predict matches injected coef")
# y = 1.5*2 + 0 = 3.0
var r = Ridge.new(1.0)
r.set_coef([1.5], 0.0)
expect(r.predict([2.0])).to_equal(3.0)
```

</details>

#### Ridge alpha=0 behaves like LinearRegression

- Ridge alpha=0 behaves like LinearRegression
- Ridge alpha=0 behaves like LinearRegression
   - Expected: lr.predict([3.0]) equals `ridge.predict([3.0])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("Ridge alpha=0 behaves like LinearRegression")
step("Ridge alpha=0 behaves like LinearRegression")
# With same coefficients, prediction is identical
var lr = LinearRegression.new()
lr.set_coef([2.0], 1.0)
var ridge = Ridge.new(0.0)
ridge.set_coef([2.0], 1.0)
expect(lr.predict([3.0])).to_equal(ridge.predict([3.0]))
```

</details>

#### intercept is preserved

- intercept is preserved
- intercept is preserved
   - Expected: r.predict([99.0]) equals `7.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("intercept is preserved")
step("intercept is preserved")
var r = Ridge.new(10.0)
r.set_coef([0.0], 7.5)
expect(r.predict([99.0])).to_equal(7.5)
```

</details>

### ml_predict_linear

#### computes dot product plus intercept

- computes dot product plus intercept
- computes dot product plus intercept
   - Expected: ml_predict_linear([2.0], 0.5, [3.0]) equals `6.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes dot product plus intercept")
step("computes dot product plus intercept")
# 2*3 + 0.5 = 6.5
expect(ml_predict_linear([2.0], 0.5, [3.0])).to_equal(6.5)
```

</details>

#### handles two features

- handles two features
- handles two features
   - Expected: ml_predict_linear([1.0, 3.0], 1.0, [2.0, 4.0]) equals `15.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles two features")
step("handles two features")
# 1*2 + 3*4 + 1 = 15
expect(ml_predict_linear([1.0, 3.0], 1.0, [2.0, 4.0])).to_equal(15.0)
```

</details>

#### zero intercept

- zero intercept
- zero intercept
   - Expected: ml_predict_linear([5.0], 0.0, [2.0]) equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("zero intercept")
step("zero intercept")
expect(ml_predict_linear([5.0], 0.0, [2.0])).to_equal(10.0)
```

</details>

#### negative coefficient

- negative coefficient
- negative coefficient
   - Expected: ml_predict_linear([-1.0], 0.0, [4.0]) equals `-4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("negative coefficient")
step("negative coefficient")
# -1*4 + 0 = -4
expect(ml_predict_linear([-1.0], 0.0, [4.0])).to_equal(-4.0)
```

</details>

### ml_mse

#### perfect prediction gives 0.0

- perfect prediction gives 0.0
- perfect prediction gives 0.0
   - Expected: ml_mse(y, y) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("perfect prediction gives 0.0")
step("perfect prediction gives 0.0")
val y = [1.0, 2.0, 3.0]
expect(ml_mse(y, y)).to_equal(0.0)
```

</details>

#### offset by 1 gives 1.0

- offset by 1 gives 1.0
- offset by 1 gives 1.0
   - Expected: ml_mse([1.0, 2.0, 3.0], [2.0, 3.0, 4.0]) equals `1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("offset by 1 gives 1.0")
step("offset by 1 gives 1.0")
# mse([1,2,3], [2,3,4]) = mean([1,1,1]) = 1.0
expect(ml_mse([1.0, 2.0, 3.0], [2.0, 3.0, 4.0])).to_equal(1.0)
```

</details>

#### single element

- single element
- single element
   - Expected: ml_mse([3.0], [1.0]) equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("single element")
step("single element")
expect(ml_mse([3.0], [1.0])).to_equal(4.0)
```

</details>

#### empty returns 0.0

- empty returns 0.0
- empty returns 0.0
   - Expected: ml_mse([], []) equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("empty returns 0.0")
step("empty returns 0.0")
expect(ml_mse([], [])).to_equal(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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
- `REQ-FEAT-SCILIB-ML-LINEAR-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bad82189adb5c5d688ac9ec5d4a9982588a8cf8d84997cb85d1a9a8bf60092f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bad82189adb5c5d688ac9ec5d4a9982588a8cf8d84997cb85d1a9a8bf60092f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bad82189adb5c5d688ac9ec5d4a9982588a8cf8d84997cb85d1a9a8bf60092f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/scilib/ml_linear_spec.spl
mirror: doc/06_spec/feature/scilib/ml_linear_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ml_linear_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ml_linear_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ml_linear_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/ml_linear_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new model is not fitted' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ml_linear_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new model has empty coef' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ml_linear_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new model has zero intercept' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
