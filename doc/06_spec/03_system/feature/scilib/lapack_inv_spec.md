# LAPACK inv / inverse Specification

> Validates the public inverse operation used by the planned math-block and

<!-- sdn-diagram:id=lapack_inv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lapack_inv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lapack_inv_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lapack_inv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LAPACK inv / inverse Specification

Validates the public inverse operation used by the planned math-block and

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-lapack-inv |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/lapack_inv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the public inverse operation used by the planned math-block and
Fortran-compatible linalg surfaces.

## Scenarios

### linalg.inv

#### returns identity for identity input

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = eye_matrix(Index.new(3))
val result = inv(a).unwrap()
expect(result.rows()).to_equal(Index.new(3))
expect(result.cols()).to_equal(Index.new(3))
expect(result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(result.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(1.0))
expect(result.get_f64_at([Index.new(2), Index.new(2)])).to_equal(Float64.new(1.0))
```

</details>

<details>
<summary>Advanced: inverts a 2x2 matrix with integer-exact inverse</summary>

#### inverts a 2x2 matrix with integer-exact inverse

1. [Float64 new
2. [Float64 new
   - Expected: result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(0.5)`
   - Expected: result.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(0.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(0.25)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = matrix_from_rows([
    [Float64.new(2.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(4.0)]])
val result = inv(a).unwrap()
expect(result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(0.5))
expect(result.get_f64_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(0.0))
expect(result.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(0.0))
expect(result.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(0.25))
```

</details>


</details>

#### returns errors for non-square and singular matrices

1. [Float64 new
2. [Float64 new
3. [Float64 new
4. [Float64 new
   - Expected: inv(non_square).is_err() is true
   - Expected: inv(singular).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val non_square = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val singular = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(2.0), Float64.new(4.0)]])
expect(inv(non_square).is_err()).to_equal(true)
expect(inv(singular).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
