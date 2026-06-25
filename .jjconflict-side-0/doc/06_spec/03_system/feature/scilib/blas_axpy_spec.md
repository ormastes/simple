# BLAS axpy Specification

> `axpy(alpha, x, y)` computes `y := alpha * x + y` (BLAS Level-1 daxpy). Public API is primitive-free: `Float64`, `NDArray<Float64>`, `LinalgError`.

<!-- sdn-diagram:id=blas_axpy_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=blas_axpy_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

blas_axpy_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=blas_axpy_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/03_system/feature/scilib/blas_axpy_spec.spl` |
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-BLAS-05, T-BLAS-06
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(0))).to_equal(Float64.new(7.0))
```

</details>

#### returns the correct element at index 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(1))).to_equal(Float64.new(10.0))
```

</details>

#### returns the correct element at index 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(2))).to_equal(Float64.new(13.0))
```

</details>

#### returns the correct element at index 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.get(Index.new(3))).to_equal(Float64.new(16.0))
```

</details>

#### result has the same shape as input

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val y = array([Float64.new(5.0), Float64.new(6.0), Float64.new(7.0), Float64.new(8.0)])
val result = axpy(Float64.new(2.0), x, y)
expect(result.shape).to_equal(Shape.new([Index.new(4)]))
```

</details>

### linalg.axpy — zero-vector and alpha=0 edge cases

#### zero-vector x

#### returns y unchanged when x is the zero vector

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_blas.md](doc/03_plan/agent_tasks/scilib_port_blas.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)


</details>
