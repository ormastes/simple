# SciPy Optimize Facade Specification

> Validates a sampled root-bracketing helper as the first optimize namespace

<!-- sdn-diagram:id=scipy_optimize_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_optimize_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_optimize_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_optimize_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Optimize Facade Specification

Validates a sampled root-bracketing helper as the first optimize namespace

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-optimize-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/scipy_optimize_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a sampled root-bracketing helper as the first optimize namespace
slice over typed `NDArray` values.

## Scenarios

### scipy.optimize bracket_root_linear

#### finds the first sign-change interval

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(-2.0), Float64.new(-1.0), Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(-3.0), Float64.new(-1.0), Float64.new(1.0), Float64.new(4.0)])
val bracket = bracket_root_linear(x, y).unwrap()
expect(bracket.left).to_equal(Float64.new(-1.0))
expect(bracket.right).to_equal(Float64.new(0.0))
```

</details>

#### returns a point bracket for exact zero samples

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0), Float64.new(2.0)])
val bracket = bracket_root_linear(x, y).unwrap()
expect(bracket.left).to_equal(Float64.new(0.0))
expect(bracket.right).to_equal(Float64.new(0.0))
```

</details>

#### returns errors for missing sign changes and bad dtypes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(2.0), Float64.new(3.0)])
expect(bracket_root_linear(x, y).is_err()).to_equal(true)
expect(bracket_root_linear(array_i64([Int64.new(0), Int64.new(1)]), y).is_err()).to_equal(true)
```

</details>

### scipy.optimize minimize_samples

#### returns the sampled minimum value and index

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(-1.0), Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(5.0), Float64.new(2.0), Float64.new(3.0), Float64.new(8.0)])
val result = minimize_samples(x, y).unwrap()
expect(result.x).to_equal(Float64.new(0.0))
expect(result.y).to_equal(Float64.new(2.0))
expect(result.index).to_equal(Index.new(1))
```

</details>

#### keeps the first minimum when values tie

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(1.0), Float64.new(1.0), Float64.new(2.0)])
val result = minimize_samples(x, y).unwrap()
expect(result.x).to_equal(Float64.new(0.0))
expect(result.index).to_equal(Index.new(0))
```

</details>

#### returns errors for empty inputs and mismatched lengths

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = array([Float64.new(0.0), Float64.new(1.0)])
expect(minimize_samples(array([]), array([])).is_err()).to_equal(true)
expect(minimize_samples(x, array([Float64.new(1.0)])).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)


</details>
