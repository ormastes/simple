# SciPy Spatial Facade Specification

> Validates a first spatial namespace slice over typed 1D F64 `NDArray` values.

<!-- sdn-diagram:id=scipy_spatial_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scipy_spatial_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scipy_spatial_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scipy_spatial_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Spatial Facade Specification

Validates a first spatial namespace slice over typed 1D F64 `NDArray` values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-spatial-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/scipy_spatial_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first spatial namespace slice over typed 1D F64 `NDArray` values.

## Scenarios

### scipy.spatial distance facade

#### computes squared euclidean distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = array([Float64.new(1.0), Float64.new(4.0), Float64.new(7.0)])
expect(squared_euclidean(left, right).unwrap()).to_equal(Float64.new(20.0))
```

</details>

#### computes euclidean distance

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = array([Float64.new(0.0), Float64.new(0.0)])
val right = array([Float64.new(3.0), Float64.new(4.0)])
val distance = euclidean(left, right).unwrap()
expect(distance.value > 4.99).to_equal(true)
expect(distance.value < 5.01).to_equal(true)
```

</details>

#### returns errors for dtype, rank, and length mismatches

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0)])
val matrix = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]).reshape(Shape.new([Index.new(2), Index.new(2)]))
expect(squared_euclidean(array_i64([Int64.new(1)]), values).is_err()).to_equal(true)
expect(squared_euclidean(matrix, matrix).is_err()).to_equal(true)
expect(squared_euclidean(values, array([Float64.new(1.0)])).is_err()).to_equal(true)
```

</details>

#### computes pairwise squared distances between point matrices

1. Float64 new
2. Float64 new
3. ]) reshape
4. Float64 new
5. Float64 new
6. ]) reshape
   - Expected: result.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: result.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(4.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(2.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = array([
    Float64.new(0.0), Float64.new(0.0),
    Float64.new(1.0), Float64.new(0.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val right = array([
    Float64.new(0.0), Float64.new(1.0),
    Float64.new(2.0), Float64.new(0.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val result = pairwise_squared_euclidean(left, right).unwrap()
expect(result.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(result.get_f64_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
expect(result.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(2.0))
expect(result.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(1.0))
```

</details>

#### returns errors for invalid pairwise distance inputs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = array([Float64.new(0.0), Float64.new(1.0)]).reshape(Shape.new([Index.new(1), Index.new(2)]))
val right = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)]).reshape(Shape.new([Index.new(1), Index.new(3)]))
expect(pairwise_squared_euclidean(left, right).is_err()).to_equal(true)
expect(pairwise_squared_euclidean(array_i64([Int64.new(1)]), right).is_err()).to_equal(true)
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
