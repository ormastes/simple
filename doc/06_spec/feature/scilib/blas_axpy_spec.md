# BLAS axpy Specification

> `axpy(alpha, x, y)` computes `y := alpha * x + y` (BLAS Level-1 daxpy). Public API is primitive-free: `Float64`, `NDArray<Float64>`, `LinalgError`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BLAS axpy Specification

`axpy(alpha, x, y)` computes `y := alpha * x + y` (BLAS Level-1 daxpy). Public API is primitive-free: `Float64`, `NDArray<Float64>`, `LinalgError`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-blas-axpy |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_blas.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/feature/scilib/blas_axpy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`axpy(alpha, x, y)` computes `y := alpha * x + y` (BLAS Level-1 daxpy).
Public API is primitive-free: `Float64`, `NDArray<Float64>`, `LinalgError`.

## Behavior

- Updates each element: `y[i] = alpha * x[i] + y[i]`
- Returns a new `NDArray<Float64>` (caller owns result; y is not mutated)
- Requires `x.shape == y.shape`; returns `Result.Err(LinalgError.DimensionMismatch)` otherwise

## Implementation Notes

Specs run under `SIMPLE_BLAS_BACKEND=mock` (set by `bin/simple test` for
`test/feature/scilib/` paths; callers must not set it in test code).
Mock backend computes correct small-N results per T-CUDA-02 (not zero-stubs).
These specs fail until T-BLAS-05 (axpy Layer B) + T-BLAS-06 (axpy Layer C) land — TDD.
No `skip()`, no `--mode=native` bypass (per `feedback_no_coverups`, AC-7).

Tasks covered: T-BLAS-05 (axpy Layer B), T-BLAS-06 (axpy Layer C).

## Scenarios

### linalg.axpy — small-N correctness

#### alpha=2.0, x=[1,2,3,4], y=[5,6,7,8]

#### returns the correct element at index 0

- returns the correct element at index 0
   - Expected: result.get(Index.new(0)) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the correct element at index 0")
# T-BLAS-05, T-BLAS-06
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(0))).to_equal(Float64.new(7.0))
```

</details>

#### returns the correct element at index 1

- returns the correct element at index 1
   - Expected: result.get(Index.new(1)) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the correct element at index 1")
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(1))).to_equal(Float64.new(10.0))
```

</details>

#### returns the correct element at index 2

- returns the correct element at index 2
   - Expected: result.get(Index.new(2)) equals `Float64.new(13.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the correct element at index 2")
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(2))).to_equal(Float64.new(13.0))
```

</details>

#### returns the correct element at index 3

- returns the correct element at index 3
   - Expected: result.get(Index.new(3)) equals `Float64.new(16.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the correct element at index 3")
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(3))).to_equal(Float64.new(16.0))
```

</details>

#### result has the same shape as input

- result has the same shape as input
   - Expected: result.shape equals `Shape.new([Index.new(4)])`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("result has the same shape as input")
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.shape).to_equal(Shape.new([Index.new(4)]))
```

</details>

### linalg.axpy — zero-vector and alpha=0 edge cases

#### zero-vector x

#### returns y unchanged when x is the zero vector

- returns y unchanged when x is the zero vector
   - Expected: result.get(Index.new(0)) equals `Float64.new(3.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(5.0)`
   - Expected: result.get(Index.new(2)) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns y unchanged when x is the zero vector")
# T-BLAS-05: zero-vector path
val x = array([Float64.new(0.0), Float64.new(0.0), Float64.new(0.0)])
val y = array([Float64.new(3.0), Float64.new(5.0), Float64.new(7.0)])
val result = axpy(Float64.new(4.0), x, y)
expect(result.get(Index.new(0))).to_equal(Float64.new(3.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(5.0))
expect(result.get(Index.new(2))).to_equal(Float64.new(7.0))
```

</details>

#### alpha=0.0

#### returns y unchanged when alpha is zero

- returns y unchanged when alpha is zero
   - Expected: result.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: result.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: result.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns y unchanged when alpha is zero")
# T-BLAS-06: alpha=0 no-op path
val x = array([Float64.new(9.0), Float64.new(8.0), Float64.new(7.0)])
val y = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val result = axpy(Float64.new(0.0), x, y)
expect(result.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(result.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(result.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

### linalg.axpy — shape mismatch error

#### returns an error when x and y have different lengths

- returns an error when x and y have different lengths
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error when x and y have different lengths")
# T-BLAS-06: dimension guard
val x = array([Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val r = try_axpy(Float64.new(1.0), x, y)
expect(r.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_blas.md`
- **Design:** `doc/05_design/scilib_port_architecture.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ae16aa3e8c4e84bcc05ae5e3465583d97d6af6cbfeeb3b7b938b1710bc2defe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ae16aa3e8c4e84bcc05ae5e3465583d97d6af6cbfeeb3b7b938b1710bc2defe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ae16aa3e8c4e84bcc05ae5e3465583d97d6af6cbfeeb3b7b938b1710bc2defe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/blas_axpy_spec.spl
mirror: doc/06_spec/feature/scilib/blas_axpy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/blas_axpy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/blas_axpy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/blas_axpy_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the correct element at index 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/blas_axpy_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the correct element at index 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/blas_axpy_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the correct element at index 2' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
