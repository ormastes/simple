# DataFrame Boolean Filter Specification

> Validates `DataFrame.filter(mask: NDArray<Bool>)`, preserving heterogeneous

<!-- sdn-diagram:id=df_filter_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_filter_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_filter_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_filter_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Boolean Filter Specification

Validates `DataFrame.filter(mask: NDArray<Bool>)`, preserving heterogeneous

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-10, science-math-lib-set-pandas-core-filter |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_filter_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates `DataFrame.filter(mask: NDArray<Bool>)`, preserving heterogeneous
column dtypes while filtering rows.

## Scenarios

### DataFrame filter with boolean mask

#### filters rows and preserves Float64 and Int64 column dtypes

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
5. ]) unwrap
   - Expected: filtered.num_rows() equals `Index.new(2)`
   - Expected: filtered.num_cols() equals `Index.new(2)`
   - Expected: filtered.col(Symbol.from("price")).unwrap().get(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: filtered.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(30)`
   - Expected: filtered.dtypes().dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
    )),
    SeriesErased.I64Series(Series.from_values(
        name: Symbol.from("qty"),
        values: [Int64.new(10), Int64.new(20), Int64.new(30)]
    )),
]).unwrap()
val filtered = df.filter(array_bool([Bool.new(true), Bool.new(false), Bool.new(true)])).unwrap()
expect(filtered.num_rows()).to_equal(Index.new(2))
expect(filtered.num_cols()).to_equal(Index.new(2))
expect(filtered.col(Symbol.from("price")).unwrap().get(Index.new(1))).to_equal(Float64.new(3.0))
expect(filtered.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(30))
expect(filtered.dtypes().dtype_at(Index.new(1))).to_equal(DType.I64)
```

</details>

#### returns ShapeMismatch when mask length differs from row count

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
   - Expected: df.filter(array_bool([Bool.new(true)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
expect(df.filter(array_bool([Bool.new(true)])).is_err()).to_equal(true)
```

</details>

#### returns ShapeMismatch when mask dtype is not Bool

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
   - Expected: df.filter(array_i64([Int64.new(1), Int64.new(0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
expect(df.filter(array_i64([Int64.new(1), Int64.new(0)])).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
