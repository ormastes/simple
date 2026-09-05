# LAPACK det / determinant Specification

> Validates a scalar determinant helper over the public linalg facade.

<!-- sdn-diagram:id=lapack_det_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lapack_det_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lapack_det_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lapack_det_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LAPACK det / determinant Specification

Validates a scalar determinant helper over the public linalg facade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-lapack-det |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/lapack_det_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a scalar determinant helper over the public linalg facade.

## Scenarios

### linalg.det

#### returns one for identity matrices

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(det(eye_matrix(Index.new(3))).unwrap()).to_equal(Float64.new(1.0))
```

</details>

<details>
<summary>Advanced: computes determinant for a 2x2 matrix</summary>

#### computes determinant for a 2x2 matrix

1. [Float64 new
2. [Float64 new
   - Expected: det(a).unwrap() equals `Float64.new(-2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)]])
expect(det(a).unwrap()).to_equal(Float64.new(-2.0))
```

</details>


</details>

#### accounts for row swaps during pivoting

1. [Float64 new
2. [Float64 new
   - Expected: det(a).unwrap() equals `Float64.new(-1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(0.0), Float64.new(1.0)],
    [Float64.new(1.0), Float64.new(0.0)]])
expect(det(a).unwrap()).to_equal(Float64.new(-1.0))
```

</details>

#### returns zero for singular matrices

1. [Float64 new
2. [Float64 new
   - Expected: det(a).unwrap() equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(2.0), Float64.new(4.0)]])
expect(det(a).unwrap()).to_equal(Float64.new(0.0))
```

</details>

#### returns an error for non-square matrices

1. [Float64 new
2. [Float64 new
   - Expected: det(a).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
expect(det(a).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
