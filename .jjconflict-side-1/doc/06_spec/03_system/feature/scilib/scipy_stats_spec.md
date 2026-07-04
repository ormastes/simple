# SciPy Stats Facade Specification

> Validates the first SciPy-style namespace slice over typed `NDArray` values.

<!-- sdn-diagram:id=scipy_stats_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_stats_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_stats_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_stats_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Stats Facade Specification

Validates the first SciPy-style namespace slice over typed `NDArray` values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-stats-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/scipy_stats_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first SciPy-style namespace slice over typed `NDArray` values.

## Scenarios

### scipy.stats NDArray facade

#### computes sum, mean, population variance, and population stddev

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
expect(sum(values).unwrap()).to_equal(Float64.new(6.0))
expect(mean(values).unwrap()).to_equal(Float64.new(2.0))
expect(variance(values).unwrap()).to_equal(Float64.new(0.6666666666666666))
expect(stddev(array([Float64.new(2.0), Float64.new(4.0)])).unwrap()).to_equal(Float64.new(1.0))
```

</details>

#### returns errors for empty mean and variance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([])
expect(mean(values).is_err()).to_equal(true)
expect(variance(values).is_err()).to_equal(true)
```

</details>

#### returns UnsupportedDType for Int64 inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array_i64([Int64.new(1), Int64.new(2)])
expect(sum(values).is_err()).to_equal(true)
expect(variance(values).is_err()).to_equal(true)
expect(zscore(values).is_err()).to_equal(true)
```

</details>

#### computes population z-scores

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(2.0), Float64.new(4.0)])
val result = zscore(values).unwrap()
expect(result.len()).to_equal(Index.new(2))
expect(result.flat_f64(0)).to_equal(Float64.new(-1.0))
expect(result.flat_f64(1)).to_equal(Float64.new(1.0))
```

</details>

#### returns errors for invalid z-score inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(zscore(array([])).is_err()).to_equal(true)
expect(zscore(array([Float64.new(3.0), Float64.new(3.0)])).is_err()).to_equal(true)
```

</details>

#### computes median for odd and even Float64 arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val odd = array([Float64.new(3.0), Float64.new(1.0), Float64.new(2.0)])
val even = array([Float64.new(4.0), Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
expect(median(odd).unwrap()).to_equal(Float64.new(2.0))
expect(median(even).unwrap()).to_equal(Float64.new(2.5))
```

</details>

#### computes linear quantiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(0.0), Float64.new(10.0), Float64.new(20.0)])
expect(quantile(values, Float64.new(0.0)).unwrap()).to_equal(Float64.new(0.0))
expect(quantile(values, Float64.new(0.25)).unwrap()).to_equal(Float64.new(5.0))
expect(quantile(values, Float64.new(1.0)).unwrap()).to_equal(Float64.new(20.0))
```

</details>

#### returns errors for invalid median and quantile inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(median(array([])).is_err()).to_equal(true)
expect(quantile(array([Float64.new(1.0)]), Float64.new(-0.1)).is_err()).to_equal(true)
expect(quantile(array_i64([Int64.new(1)]), Float64.new(0.5)).is_err()).to_equal(true)
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

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
