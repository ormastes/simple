# NDArray Sort And Argsort Specification

> Validates stable 1-D sort and argsort infrastructure used by later DataFrame

<!-- sdn-diagram:id=ndarray_sort_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ndarray_sort_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ndarray_sort_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ndarray_sort_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Sort And Argsort Specification

Validates stable 1-D sort and argsort infrastructure used by later DataFrame

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-sort |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/ndarray_sort_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**DF dependency:** doc/03_plan/agent_tasks/scilib_port_df.md T-DF-19/T-DF-21

Validates stable 1-D sort and argsort infrastructure used by later DataFrame
sort/groupby work.

## Scenarios

### NDArray argsort

#### returns stable ascending indices for Float64 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array([Float64.new(3.0), Float64.new(1.0), Float64.new(3.0), Float64.new(2.0)])
val idx = a.argsort()
expect(idx.dtype).to_equal(DType.I64)
expect(idx.get(Index.new(0))).to_equal(Int64.new(1))
expect(idx.get(Index.new(1))).to_equal(Int64.new(3))
expect(idx.get(Index.new(2))).to_equal(Int64.new(0))
expect(idx.get(Index.new(3))).to_equal(Int64.new(2))
```

</details>

#### returns ascending indices for Int64 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = array_i64([Int64.new(9), Int64.new(-2), Int64.new(4)])
val idx = a.argsort()
expect(idx.get(Index.new(0))).to_equal(Int64.new(1))
expect(idx.get(Index.new(1))).to_equal(Int64.new(2))
expect(idx.get(Index.new(2))).to_equal(Int64.new(0))
```

</details>

### NDArray sort

#### sorts Float64 values using argsort and gather

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sorted = array([Float64.new(3.0), Float64.new(1.0), Float64.new(2.0)]).sort()
expect(sorted.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(sorted.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(sorted.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### sorts Int64 values without changing dtype

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sorted = array_i64([Int64.new(3), Int64.new(1), Int64.new(2)]).sort()
expect(sorted.dtype).to_equal(DType.I64)
expect(sorted.get(Index.new(0))).to_equal(Int64.new(1))
expect(sorted.get(Index.new(2))).to_equal(Int64.new(3))
```

</details>

#### returns UnsupportedDType for Bool argsort

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = array_bool([Bool.new(true), Bool.new(false)]).try_argsort()
expect(result.is_err()).to_equal(true)
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
