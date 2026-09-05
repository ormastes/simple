# NDArray Axis Reduction Specification

> Validates the first axis-aware reduction slice: 2-D Float64 `sum_axis`.

<!-- sdn-diagram:id=ndarray_axis_reduction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_axis_reduction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_axis_reduction_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_axis_reduction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Axis Reduction Specification

Validates the first axis-aware reduction slice: 2-D Float64 `sum_axis`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-axis-reductions |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_axis_reduction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first axis-aware reduction slice: 2-D Float64 `sum_axis`.

## Scenarios

### NDArray sum_axis

<details>
<summary>Advanced: sums a 2-D matrix over axis 0 into column totals</summary>

#### sums a 2-D matrix over axis 0 into column totals

1. Float64 new
2. Float64 new
3. ]) reshape
   - Expected: out.shape equals `Shape.new([Index.new(3)])`
   - Expected: out.get(Index.new(0)) equals `Float64.new(5.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(7.0)`
   - Expected: out.get(Index.new(2)) equals `Float64.new(9.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([
    Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
    Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)
]).reshape(Shape.new([Index.new(2), Index.new(3)]))
val out = a.sum_axis(Axis.new(0))
expect(out.shape).to_equal(Shape.new([Index.new(3)]))
expect(out.get(Index.new(0))).to_equal(Float64.new(5.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(7.0))
expect(out.get(Index.new(2))).to_equal(Float64.new(9.0))
```

</details>


</details>

<details>
<summary>Advanced: sums a 2-D matrix over axis 1 into row totals</summary>

#### sums a 2-D matrix over axis 1 into row totals

1. Float64 new
2. Float64 new
3. ]) reshape
   - Expected: out.shape equals `Shape.new([Index.new(2)])`
   - Expected: out.get(Index.new(0)) equals `Float64.new(6.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(15.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([
    Float64.new(1.0), Float64.new(2.0), Float64.new(3.0),
    Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)
]).reshape(Shape.new([Index.new(2), Index.new(3)]))
val out = a.sum_axis(Axis.new(1))
expect(out.shape).to_equal(Shape.new([Index.new(2)]))
expect(out.get(Index.new(0))).to_equal(Float64.new(6.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(15.0))
```

</details>


</details>

#### supports negative axis indexing

1. Float64 new
2. Float64 new
3. ]) reshape
   - Expected: out.get(Index.new(0)) equals `Float64.new(3.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([
    Float64.new(1.0), Float64.new(2.0),
    Float64.new(3.0), Float64.new(4.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val out = a.sum_axis(Axis.new(-1))
expect(out.get(Index.new(0))).to_equal(Float64.new(3.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(7.0))
```

</details>

#### returns errors for non-2D input, bad axis, and unsupported dtype

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val one_d = array([Float64.new(1.0), Float64.new(2.0)])
expect(one_d.try_sum_axis(Axis.new(0)).is_err()).to_equal(true)
val two_d = one_d.reshape(Shape.new([Index.new(1), Index.new(2)]))
expect(two_d.try_sum_axis(Axis.new(2)).is_err()).to_equal(true)
val ints = array_i64([Int64.new(1), Int64.new(2)]).reshape(Shape.new([Index.new(1), Index.new(2)]))
expect(ints.try_sum_axis(Axis.new(1)).is_err()).to_equal(true)
```

</details>

### NDArray mean_axis

#### computes column means over axis 0

1. Float64 new
2. Float64 new
3. ]) reshape
   - Expected: out.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([
    Float64.new(1.0), Float64.new(2.0),
    Float64.new(3.0), Float64.new(4.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val out = a.mean_axis(Axis.new(0))
expect(out.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(3.0))
```

</details>

#### computes row means over axis 1

1. Float64 new
2. Float64 new
3. ]) reshape
   - Expected: out.get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: out.get(Index.new(1)) equals `Float64.new(6.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([
    Float64.new(1.0), Float64.new(3.0),
    Float64.new(5.0), Float64.new(7.0)
]).reshape(Shape.new([Index.new(2), Index.new(2)]))
val out = a.mean_axis(Axis.new(1))
expect(out.get(Index.new(0))).to_equal(Float64.new(2.0))
expect(out.get(Index.new(1))).to_equal(Float64.new(6.0))
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
