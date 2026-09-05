# NDArray Concatenate And Stack Specification

> Validates the first NumPy-core shape-composition slice. This intentionally

<!-- sdn-diagram:id=ndarray_concat_stack_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_concat_stack_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_concat_stack_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_concat_stack_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Concatenate And Stack Specification

Validates the first NumPy-core shape-composition slice. This intentionally

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-concat-stack |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_concat_stack_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first NumPy-core shape-composition slice. This intentionally
covers 1-D inputs only; axis-general concatenate/stack is a later phase.

## Scenarios

### NDArray concatenate

#### concatenates Float64 1-D arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(1.0), Float64.new(2.0)])
val b = array([Float64.new(3.0)])
val c = concatenate([a, b])
expect(c.shape).to_equal(Shape.new([Index.new(3)]))
expect(c.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(c.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### concatenates Int64 arrays without changing dtype

1. array i64
2. array i64
   - Expected: c.dtype equals `DType.I64`
   - Expected: c.get(Index.new(3)) equals `Int64.new(4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = concatenate([
    array_i64([Int64.new(1), Int64.new(2)]),
    array_i64([Int64.new(3), Int64.new(4)])
])
expect(c.dtype).to_equal(DType.I64)
expect(c.get(Index.new(3))).to_equal(Int64.new(4))
```

</details>

#### rejects empty input and mixed dtypes

1. array
2. array i64
   - Expected: mixed.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [NDArray] = []
expect(try_concatenate(empty).is_err()).to_equal(true)
val mixed = try_concatenate([
    array([Float64.new(1.0)]),
    array_i64([Int64.new(1)])
])
expect(mixed.is_err()).to_equal(true)
```

</details>

### NDArray stack

#### stacks equal-length Float64 vectors into a 2-D array

1. array
2. array
   - Expected: s.shape equals `Shape.new([Index.new(2), Index.new(2)])`
   - Expected: s.get_at([Index.new(0), Index.new(1)]) equals `Float64.new(2.0)`
   - Expected: s.get_at([Index.new(1), Index.new(0)]) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = stack([
    array([Float64.new(1.0), Float64.new(2.0)]),
    array([Float64.new(3.0), Float64.new(4.0)])
])
expect(s.shape).to_equal(Shape.new([Index.new(2), Index.new(2)]))
expect(s.get_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(2.0))
expect(s.get_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(3.0))
```

</details>

#### returns UnsupportedDType for Bool stack in this 1-D v1 slice

1. array bool
2. array bool
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = try_stack([
    array_bool([Bool.new(true), Bool.new(false)]),
    array_bool([Bool.new(false), Bool.new(true)])
])
expect(result.is_err()).to_equal(true)
```

</details>

#### rejects mismatched vector lengths

1. array
2. array
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = try_stack([
    array([Float64.new(1.0)]),
    array([Float64.new(2.0), Float64.new(3.0)])
])
expect(result.is_err()).to_equal(true)
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
