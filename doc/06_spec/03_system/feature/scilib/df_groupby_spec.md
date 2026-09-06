# DataFrame GroupBy Specification

> Validates the first pandas-style groupby aggregation slice over labeled

<!-- sdn-diagram:id=df_groupby_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_groupby_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_groupby_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_groupby_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame GroupBy Specification

Validates the first pandas-style groupby aggregation slice over labeled

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-df-groupby-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_groupby_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first pandas-style groupby aggregation slice over labeled
`DataFrame` columns.

## Scenarios

### DataFrame groupby aggregations

#### groups by an Int64 key and computes sums

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: grouped.num_rows() equals `Index.new(2)`
   - Expected: grouped.col(Symbol.from("team")).unwrap().values.flat_i64(0) equals `Int64.new(1)`
   - Expected: grouped.col(Symbol.from("points")).unwrap().values.flat_f64(0) equals `Float64.new(17.0)`
   - Expected: grouped.col(Symbol.from("team")).unwrap().values.flat_i64(1) equals `Int64.new(2)`
   - Expected: grouped.col(Symbol.from("points")).unwrap().values.flat_f64(1) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("team"), values: array_i64([Int64.new(1), Int64.new(2), Int64.new(1)]), dtype: DType.I64, missing: [Bool.new(false), Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("points"), [Float64.new(10.0), Float64.new(5.0), Float64.new(7.0)]))
]).unwrap()
val grouped = df.groupby_sum(Symbol.from("team"), Symbol.from("points")).unwrap()
expect(grouped.num_rows()).to_equal(Index.new(2))
expect(grouped.col(Symbol.from("team")).unwrap().values.flat_i64(0)).to_equal(Int64.new(1))
expect(grouped.col(Symbol.from("points")).unwrap().values.flat_f64(0)).to_equal(Float64.new(17.0))
expect(grouped.col(Symbol.from("team")).unwrap().values.flat_i64(1)).to_equal(Int64.new(2))
expect(grouped.col(Symbol.from("points")).unwrap().values.flat_f64(1)).to_equal(Float64.new(5.0))
```

</details>

#### groups by a Float64 key and computes means

1. SeriesErased F64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: grouped.num_rows() equals `Index.new(2)`
   - Expected: grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(0) equals `Float64.new(1.5)`
   - Expected: grouped.col(Symbol.from("score")).unwrap().values.flat_f64(0) equals `Float64.new(3.0)`
   - Expected: grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(1) equals `Float64.new(2.5)`
   - Expected: grouped.col(Symbol.from("score")).unwrap().values.flat_f64(1) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series(name: Symbol.from("bucket"), values: array([Float64.new(1.5), Float64.new(1.5), Float64.new(2.5)]), dtype: DType.F64, missing: [Bool.new(false), Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(2.0), Float64.new(4.0), Float64.new(10.0)]))
]).unwrap()
val grouped = df.groupby_mean(Symbol.from("bucket"), Symbol.from("score")).unwrap()
expect(grouped.num_rows()).to_equal(Index.new(2))
expect(grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(0)).to_equal(Float64.new(1.5))
expect(grouped.col(Symbol.from("score")).unwrap().values.flat_f64(0)).to_equal(Float64.new(3.0))
expect(grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(1)).to_equal(Float64.new(2.5))
expect(grouped.col(Symbol.from("score")).unwrap().values.flat_f64(1)).to_equal(Float64.new(10.0))
```

</details>

#### returns errors for missing columns and non-F64 value columns

1. SeriesErased I64Series
2. SeriesErased I64Series
3. ]) unwrap
   - Expected: df.groupby_sum(Symbol.from("missing"), Symbol.from("points")).is_err() is true
   - Expected: df.groupby_sum(Symbol.from("team"), Symbol.from("points")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("team"), values: array_i64([Int64.new(1)]), dtype: DType.I64, missing: [Bool.new(false)])),
    SeriesErased.I64Series(Series(name: Symbol.from("points"), values: array_i64([Int64.new(10)]), dtype: DType.I64, missing: [Bool.new(false)]))
]).unwrap()
expect(df.groupby_sum(Symbol.from("missing"), Symbol.from("points")).is_err()).to_equal(true)
expect(df.groupby_sum(Symbol.from("team"), Symbol.from("points")).is_err()).to_equal(true)
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

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
