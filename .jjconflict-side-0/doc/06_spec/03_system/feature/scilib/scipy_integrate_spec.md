# SciPy Integrate Facade Specification

> Validates the first SciPy-style integration namespace slice over typed

<!-- sdn-diagram:id=scipy_integrate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_integrate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_integrate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_integrate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Integrate Facade Specification

Validates the first SciPy-style integration namespace slice over typed

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-integrate-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/scipy_integrate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first SciPy-style integration namespace slice over typed
`NDArray` values.

## Scenarios

### scipy.integrate trapezoid

#### integrates y=x over [0, 2] using sampled points

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
expect(trapezoid(y, x).unwrap()).to_equal(Float64.new(2.0))
```

</details>

#### integrates constant values with non-unit spacing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(2.0), Float64.new(5.0)])
val y = array([Float64.new(3.0), Float64.new(3.0), Float64.new(3.0)])
expect(trapezoid(y, x).unwrap()).to_equal(Float64.new(15.0))
```

</details>

#### returns errors for mismatched lengths and unsupported dtypes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0)])
expect(trapezoid(y, x).is_err()).to_equal(true)
expect(trapezoid(array_i64([Int64.new(1), Int64.new(2)]), x).is_err()).to_equal(true)
```

</details>

### scipy.integrate cumulative_trapezoid

#### returns cumulative area with an initial zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val result = cumulative_trapezoid(y, x).unwrap()
expect(result.len()).to_equal(Index.new(3))
expect(result.flat_f64(0)).to_equal(Float64.new(0.0))
expect(result.flat_f64(1)).to_equal(Float64.new(0.5))
expect(result.flat_f64(2)).to_equal(Float64.new(2.0))
```

</details>

#### returns errors for mismatched lengths and unsupported dtypes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0)])
expect(cumulative_trapezoid(array([Float64.new(0.0)]), x).is_err()).to_equal(true)
expect(cumulative_trapezoid(array_i64([Int64.new(1), Int64.new(2)]), x).is_err()).to_equal(true)
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
