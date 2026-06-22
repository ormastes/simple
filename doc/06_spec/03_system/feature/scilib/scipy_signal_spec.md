# SciPy Signal Facade Specification

> Validates a first signal-processing namespace slice over typed `NDArray`

<!-- sdn-diagram:id=scipy_signal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_signal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_signal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_signal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Signal Facade Specification

Validates a first signal-processing namespace slice over typed `NDArray`

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-signal-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/scipy_signal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first signal-processing namespace slice over typed `NDArray`
values.

## Scenarios

### scipy.signal NDArray facade

#### computes full one-dimensional convolution

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val weights = array([Float64.new(1.0), Float64.new(1.0)])
val result = convolve_full(values, weights).unwrap()
expect(result.len()).to_equal(Index.new(4))
expect(result.flat_f64(0)).to_equal(Float64.new(1.0))
expect(result.flat_f64(1)).to_equal(Float64.new(3.0))
expect(result.flat_f64(2)).to_equal(Float64.new(5.0))
expect(result.flat_f64(3)).to_equal(Float64.new(3.0))
```

</details>

#### computes a valid moving average

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(2.0), Float64.new(4.0), Float64.new(6.0), Float64.new(8.0)])
val result = moving_average(values, Index.new(2)).unwrap()
expect(result.len()).to_equal(Index.new(3))
expect(result.flat_f64(0)).to_equal(Float64.new(3.0))
expect(result.flat_f64(1)).to_equal(Float64.new(5.0))
expect(result.flat_f64(2)).to_equal(Float64.new(7.0))
```

</details>

#### computes full one-dimensional correlation

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = array([Float64.new(4.0), Float64.new(5.0)])
val result = correlate_full(left, right).unwrap()
expect(result.len()).to_equal(Index.new(4))
expect(result.flat_f64(0)).to_equal(Float64.new(5.0))
expect(result.flat_f64(1)).to_equal(Float64.new(14.0))
expect(result.flat_f64(2)).to_equal(Float64.new(23.0))
expect(result.flat_f64(3)).to_equal(Float64.new(12.0))
```

</details>

#### computes first differences

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(3.0), Float64.new(5.0), Float64.new(4.0)])
val result = first_difference(values).unwrap()
expect(result.len()).to_equal(Index.new(2))
expect(result.flat_f64(0)).to_equal(Float64.new(2.0))
expect(result.flat_f64(1)).to_equal(Float64.new(-1.0))
```

</details>

#### returns errors for unsupported dtype and invalid window

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0)])
expect(convolve_full(array_i64([Int64.new(1)]), values).is_err()).to_equal(true)
expect(correlate_full(values, array_i64([Int64.new(1)])).is_err()).to_equal(true)
expect(moving_average(values, Index.new(0)).is_err()).to_equal(true)
expect(moving_average(values, Index.new(3)).is_err()).to_equal(true)
expect(first_difference(array([Float64.new(1.0)])).is_err()).to_equal(true)
expect(first_difference(array_i64([Int64.new(1), Int64.new(2)])).is_err()).to_equal(true)
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
