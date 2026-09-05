# LAPACK gesv / solve Specification

> `solve(A, b)` solves the linear system Ax = b for x (LAPACK dgesv). Public API is primitive-free: `Matrix<Float64>`, `Vector<Float64>`, `Result<Vector<Float64>, LinalgError>`. The pivot array is fully hidden inside Layer B (T-LAPACK-07: no raw `int*` leak at Layer C).

<!-- sdn-diagram:id=lapack_gesv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lapack_gesv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lapack_gesv_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lapack_gesv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LAPACK gesv / solve Specification

`solve(A, b)` solves the linear system Ax = b for x (LAPACK dgesv). Public API is primitive-free: `Matrix<Float64>`, `Vector<Float64>`, `Result<Vector<Float64>, LinalgError>`. The pivot array is fully hidden inside Layer B (T-LAPACK-07: no raw `int*` leak at Layer C).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-lapack-gesv |
| Category | Stdlib |
| Difficulty | 3/5 |
| Status | Draft |
| Plan | doc/03_plan/agent_tasks/scilib_port_lapack.md |
| Design | doc/05_design/scilib_port_architecture.md |
| Source | `test/03_system/feature/scilib/lapack_gesv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`solve(A, b)` solves the linear system Ax = b for x (LAPACK dgesv).
Public API is primitive-free: `Matrix<Float64>`, `Vector<Float64>`,
`Result<Vector<Float64>, LinalgError>`. The pivot array is fully hidden inside
Layer B (T-LAPACK-07: no raw `int*` leak at Layer C).

## Behavior

- Solves `A * x = b`; returns `Result.Ok(x)` where `x` is `Vector<Float64>`
- A must be square (n×n); b must have length n
- Singular A (det≈0) returns `Result.Err(LinalgError.Singular)` — info != 0 path
- Non-square A returns `Result.Err(LinalgError.DimensionMismatch(...))`
- Identity-matrix shortcut: solution is exactly b

## Numerical Verification

Lower-triangular 3×3 system (det=1, no cancellation):
  A = [[1,0,0],[2,1,0],[3,4,1]], b = [1,4,15]
  Forward-substitution:
    x[0] = 1
    x[1] = 4 - 2*1 = 2
    x[2] = 15 - 3*1 - 4*2 = 4
  Answer: x = [1, 2, 4]  (all integer-exact in Float64)

## Implementation Notes

Specs run under `SIMPLE_BLAS_BACKEND=mock` (set by `bin/simple test` for
`test/feature/scilib/` paths). Mock computes correct small-N results (T-CUDA-02).
These specs fail until T-LAPACK-07 (gesv Layer B) + T-LAPACK-12 (solve Layer C) land — TDD.
No `skip()`, no `--mode=native` bypass (AC-7 / feedback_no_coverups).
Pivot type is `Pivot` (wrapped); no raw int* visible at Layer C boundary.

Tasks covered: T-LAPACK-07 (gesv Layer B, pivot hidden),
T-LAPACK-12 (solve Layer C public API), T-LAPACK-15 (gesv interp-mode spec).

## Scenarios

### linalg.solve — 3x3 lower-triangular system

#### A lower-triangular, b = [1,4,15]

#### solves and returns x[0]=1.0

1. [Float64 new
2. [Float64 new
3. [Float64 new
   - Expected: result.is_ok() is true
   - Expected: x.get_f64(Index.new(0)) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-LAPACK-07, T-LAPACK-15
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(2.0), Float64.new(1.0), Float64.new(0.0)],
    [Float64.new(3.0), Float64.new(4.0), Float64.new(1.0)]])
val b = vector_from([Float64.new(1.0), Float64.new(4.0), Float64.new(15.0)])
val result = solve(a, b)
expect(result.is_ok()).to_equal(true)
val x = result.unwrap()
expect(x.get_f64(Index.new(0))).to_equal(Float64.new(1.0))
```

</details>

#### solves and returns x[1]=2.0

1. [Float64 new
2. [Float64 new
3. [Float64 new
   - Expected: x.get_f64(Index.new(1)) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(2.0), Float64.new(1.0), Float64.new(0.0)],
    [Float64.new(3.0), Float64.new(4.0), Float64.new(1.0)]])
val b = vector_from([Float64.new(1.0), Float64.new(4.0), Float64.new(15.0)])
val result = solve(a, b)
val x = result.unwrap()
expect(x.get_f64(Index.new(1))).to_equal(Float64.new(2.0))
```

</details>

#### solves and returns x[2]=4.0

1. [Float64 new
2. [Float64 new
3. [Float64 new
   - Expected: x.get_f64(Index.new(2)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(2.0), Float64.new(1.0), Float64.new(0.0)],
    [Float64.new(3.0), Float64.new(4.0), Float64.new(1.0)]])
val b = vector_from([Float64.new(1.0), Float64.new(4.0), Float64.new(15.0)])
val result = solve(a, b)
val x = result.unwrap()
expect(x.get_f64(Index.new(2))).to_equal(Float64.new(4.0))
```

</details>

#### result vector has length 3

1. [Float64 new
2. [Float64 new
3. [Float64 new
   - Expected: x.len() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(2.0), Float64.new(1.0), Float64.new(0.0)],
    [Float64.new(3.0), Float64.new(4.0), Float64.new(1.0)]])
val b = vector_from([Float64.new(1.0), Float64.new(4.0), Float64.new(15.0)])
val result = solve(a, b)
val x = result.unwrap()
expect(x.len()).to_equal(Index.new(3))
```

</details>

### linalg.solve — identity matrix shortcut

#### A = 3x3 identity, b = [7, 3, 9]

#### returns x equal to b

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-LAPACK-12: identity shortcut path
val a = eye_matrix(Index.new(3))
val b = vector_from([Float64.new(7.0), Float64.new(3.0), Float64.new(9.0)])
val result = solve(a, b)
expect(result.is_ok()).to_equal(true)
val x = result.unwrap()
expect(x.get_f64(Index.new(0))).to_equal(Float64.new(7.0))
expect(x.get_f64(Index.new(1))).to_equal(Float64.new(3.0))
expect(x.get_f64(Index.new(2))).to_equal(Float64.new(9.0))
```

</details>

### linalg.solve — error paths

#### singular A

#### returns an error with Singular variant for rank-deficient A

1. [Float64 new
2. [Float64 new
3. [Float64 new
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-LAPACK-07: info != 0 path; pivot wrapper hidden
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(0.0), Float64.new(0.0), Float64.new(0.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = vector_from([Float64.new(1.0), Float64.new(0.0), Float64.new(1.0)])
val r = solve(a, b)
expect(r.is_err()).to_equal(true)
```

</details>

#### non-square A

#### returns an error for non-square A

1. [Float64 new
2. [Float64 new
   - Expected: r.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-LAPACK-12: non-square guard
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val b = vector_from([Float64.new(1.0), Float64.new(2.0)])
val r = solve(a, b)
expect(r.is_err()).to_equal(true)
```

</details>

#### dimension mismatch between A and b

#### returns an error when b length does not match A order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# T-LAPACK-12: A.rows != b.len guard
val a = eye_matrix(Index.new(3))
val b = vector_from([Float64.new(1.0), Float64.new(2.0)])
val r = solve(a, b)
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

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_lapack.md](doc/03_plan/agent_tasks/scilib_port_lapack.md)
- **Design:** [doc/05_design/scilib_port_architecture.md](doc/05_design/scilib_port_architecture.md)


</details>
