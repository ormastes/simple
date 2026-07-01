# NDArray Reduction Specification

> Validates the first NumPy-core reduction slice for F64 NDArrays. Axis-aware

<!-- sdn-diagram:id=ndarray_reduction_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_reduction_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_reduction_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_reduction_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Reduction Specification

Validates the first NumPy-core reduction slice for F64 NDArrays. Axis-aware

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-reductions |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_reduction_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first NumPy-core reduction slice for F64 NDArrays. Axis-aware
reductions are planned separately; this spec covers whole-array reductions and
their Result-based error paths.

## Scenarios

### NDArray whole-array reductions

#### computes sum, mean, min, max, and argmax over a 1-D Float64 array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(2.0), Float64.new(-1.0), Float64.new(5.0), Float64.new(4.0)])
expect(a.sum()).to_equal(Float64.new(10.0))
expect(a.mean()).to_equal(Float64.new(2.5))
expect(a.min()).to_equal(Float64.new(-1.0))
expect(a.max()).to_equal(Float64.new(5.0))
expect(a.argmax()).to_equal(Index.new(2))
```

</details>

#### computes contiguous Float64 sum and mean through SIMD chunks with a scalar tail

1. Float64 new
2. Float64 new
   - Expected: a.sum() equals `Float64.new(21.0)`
   - Expected: a.mean() equals `Float64.new(3.5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([
    Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0),
    Float64.new(5.0), Float64.new(6.0)])
expect(a.sum()).to_equal(Float64.new(21.0))
expect(a.mean()).to_equal(Float64.new(3.5))
```

</details>

#### computes contiguous Float32 sum and mean through SIMD chunks with a scalar tail

1. Float32 new
2. Float32 new
   - Expected: a.sum_f32() equals `Float32.new(21.0)`
   - Expected: a.mean_f32() equals `Float32.new(3.5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_f32([
    Float32.new(1.0), Float32.new(2.0), Float32.new(3.0), Float32.new(4.0),
    Float32.new(5.0), Float32.new(6.0)])
expect(a.sum_f32()).to_equal(Float32.new(21.0))
expect(a.mean_f32()).to_equal(Float32.new(3.5))
```

</details>

#### reduces a strided slice using logical element order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0), Float64.new(4.0), Float64.new(5.0)])
val every_other = a.slice(Slice.new(Index.new(0), Index.new(5), Index.new(2)))
expect(every_other.sum()).to_equal(Float64.new(9.0))
expect(every_other.mean()).to_equal(Float64.new(3.0))
expect(every_other.max()).to_equal(Float64.new(5.0))
```

</details>

#### returns errors for empty mean/min/max/argmax

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty = array([])
expect(empty.try_mean().is_err()).to_equal(true)
expect(empty.try_min().is_err()).to_equal(true)
expect(empty.try_max().is_err()).to_equal(true)
expect(empty.try_argmax().is_err()).to_equal(true)
```

</details>

#### returns UnsupportedDType for Int64 reductions through Result APIs

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ints = array_i64([Int64.new(1), Int64.new(2)])
expect(ints.try_sum().is_err()).to_equal(true)
expect(ints.try_sum_f32().is_err()).to_equal(true)
expect(ints.try_mean_f32().is_err()).to_equal(true)
expect(ints.try_min().is_err()).to_equal(true)
expect(ints.try_max().is_err()).to_equal(true)
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
