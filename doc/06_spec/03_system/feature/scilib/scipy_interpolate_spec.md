# SciPy Interpolate Facade Specification

> Validates a first interpolation namespace slice over typed `NDArray` values.

<!-- sdn-diagram:id=scipy_interpolate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_interpolate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_interpolate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_interpolate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Interpolate Facade Specification

Validates a first interpolation namespace slice over typed `NDArray` values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-interpolate-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/scipy_interpolate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first interpolation namespace slice over typed `NDArray` values.

## Scenarios

### scipy.interpolate interp1d_linear

#### linearly interpolates inside a sampled interval

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(10.0)])
val y = array([Float64.new(0.0), Float64.new(20.0)])
expect(interp1d_linear(x, y, Float64.new(2.5)).unwrap()).to_equal(Float64.new(5.0))
```

</details>

#### uses the containing interval in a multi-point sample

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(3.0)])
val y = array([Float64.new(0.0), Float64.new(2.0), Float64.new(6.0)])
expect(interp1d_linear(x, y, Float64.new(2.0)).unwrap()).to_equal(Float64.new(4.0))
```

</details>

#### returns errors for out-of-range query and bad dtype

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0), Float64.new(1.0)])
expect(interp1d_linear(x, y, Float64.new(2.0)).is_err()).to_equal(true)
expect(interp1d_linear(array_i64([Int64.new(0), Int64.new(1)]), y, Float64.new(0.5)).is_err()).to_equal(true)
```

</details>

#### linearly interpolates an array of query points

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(10.0)])
val y = array([Float64.new(0.0), Float64.new(20.0)])
val queries = array([Float64.new(0.0), Float64.new(2.5), Float64.new(10.0)])
val result = interp1d_linear_array(x, y, queries).unwrap()
expect(result.len()).to_equal(Index.new(3))
expect(result.flat_f64(0)).to_equal(Float64.new(0.0))
expect(result.flat_f64(1)).to_equal(Float64.new(5.0))
expect(result.flat_f64(2)).to_equal(Float64.new(20.0))
```

</details>

#### returns errors for invalid query arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0), Float64.new(1.0)])
expect(interp1d_linear_array(x, y, array_i64([Int64.new(0)])).is_err()).to_equal(true)
expect(interp1d_linear_array(x, y, array([Float64.new(2.0)])).is_err()).to_equal(true)
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


</details>
