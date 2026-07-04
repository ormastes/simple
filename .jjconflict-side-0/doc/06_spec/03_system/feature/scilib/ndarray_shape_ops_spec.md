# NDArray Shape Operation Specification

> Validates reshape, flatten, squeeze, and transpose shape metadata operations.

<!-- sdn-diagram:id=ndarray_shape_ops_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_shape_ops_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_shape_ops_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_shape_ops_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Shape Operation Specification

Validates reshape, flatten, squeeze, and transpose shape metadata operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-ndarray-shape-ops |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_shape_ops_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates reshape, flatten, squeeze, and transpose shape metadata operations.

## Scenarios

### NDArray reshape

#### reshapes a contiguous vector without changing logical values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)])
val matrix = values.reshape(Shape.new([Index.new(2), Index.new(2)]))
expect(matrix.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(matrix.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
```

</details>

#### returns errors for invalid reshape requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
expect(values.try_reshape(Shape.new([Index.new(2), Index.new(2)])).is_err()).to_equal(true)
expect(values.try_reshape(Shape.new([Index.new(-3)])).is_err()).to_equal(true)
```

</details>

### NDArray flatten and squeeze

#### flattens a strided view in logical order

1. Shape new
   - Expected: flattened.shape equals `Shape.new([Index.new(4)])`
   - Expected: flattened.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: flattened.get(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: flattened.get(Index.new(2)) equals `Float64.new(2.0)`
   - Expected: flattened.get(Index.new(3)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0)]).reshape(
    Shape.new([Index.new(2), Index.new(2)])
)
val transposed = matrix.transpose()
val flattened = transposed.flatten()
expect(flattened.shape).to_equal(Shape.new([Index.new(4)]))
expect(flattened.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(flattened.get(Index.new(1))).to_equal(Float64.new(3.0))
expect(flattened.get(Index.new(2))).to_equal(Float64.new(2.0))
expect(flattened.get(Index.new(3))).to_equal(Float64.new(4.0))
```

</details>

#### removes size-one dimensions with squeeze

1. Shape new
   - Expected: squeezed.shape equals `Shape.new([Index.new(2)])`
   - Expected: squeezed.get(Index.new(1)) equals `Float64.new(8.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(7.0), Float64.new(8.0)]).reshape(
    Shape.new([Index.new(1), Index.new(2), Index.new(1)])
)
val squeezed = values.squeeze()
expect(squeezed.shape).to_equal(Shape.new([Index.new(2)]))
expect(squeezed.get(Index.new(1))).to_equal(Float64.new(8.0))
```

</details>

### NDArray transpose

<details>
<summary>Advanced: transposes a two-dimensional matrix as a strided view</summary>

#### transposes a two-dimensional matrix as a strided view

1. Shape new
   - Expected: transposed.shape equals `Shape.new([Index.new(3), Index.new(2)])`
   - Expected: transposed.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(4.0)`
   - Expected: transposed.get_at([Index.new(2), Index.new(1)]) equals `Float64.new(6.0)`
   - Expected: transposed.layout equals `Layout.Strided`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val matrix = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]).reshape(
    Shape.new([Index.new(2), Index.new(3)])
)
val transposed = matrix.transpose()
expect(transposed.shape).to_equal(Shape.new([Index.new(3), Index.new(2)]))
expect(transposed.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(4.0))
expect(transposed.get_at([Index.new(2), Index.new(1)])).to_equal(Float64.new(6.0))
expect(transposed.layout).to_equal(Layout.Strided)
```

</details>


</details>

#### returns errors for invalid transpose axes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = array([Float64.new(1.0), Float64.new(2.0)])
expect(values.try_transpose_axes(Axis.new(0), Axis.new(1)).is_err()).to_equal(true)
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
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
