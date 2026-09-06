# DataFrame Indexing Specification

> Validates row lookup and row selection helpers for pandas-style indexing.

<!-- sdn-diagram:id=df_indexing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_indexing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_indexing_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_indexing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Indexing Specification

Validates row lookup and row selection helpers for pandas-style indexing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-df-indexing-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_indexing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates row lookup and row selection helpers for pandas-style indexing.

## Scenarios

### DataFrame row indexing

#### returns a typed row by position

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: row.len() equals `2`
   - Expected: row[0].key equals `Symbol.from("id")`
   - Expected: row[0].value equals `DfValue.I64(Int64.new(20))`
   - Expected: row[1].key equals `Symbol.from("score")`
   - Expected: row[1].value equals `DfValue.F64(Float64.new(2.5))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("id"), values: array_i64([Int64.new(10), Int64.new(20)]), dtype: DType.I64, missing: [Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.5), Float64.new(2.5)]))
]).unwrap()
val row = df.row(Index.new(1)).unwrap()
expect(row.len()).to_equal(2)
expect(row[0].key).to_equal(Symbol.from("id"))
expect(row[0].value).to_equal(DfValue.I64(Int64.new(20)))
expect(row[1].key).to_equal(Symbol.from("score"))
expect(row[1].value).to_equal(DfValue.F64(Float64.new(2.5)))
```

</details>

#### returns an error for out-of-range row lookup

1. SeriesErased F64Series
2. ]) unwrap
   - Expected: df.row(Index.new(-1)).is_err() is true
   - Expected: df.row(Index.new(1)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.0)]))
]).unwrap()
expect(df.row(Index.new(-1)).is_err()).to_equal(true)
expect(df.row(Index.new(1)).is_err()).to_equal(true)
```

</details>

#### takes rows in caller-specified order

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: taken.num_rows() equals `Index.new(2)`
   - Expected: taken.col(Symbol.from("id")).unwrap().values.flat_i64(0) equals `Int64.new(30)`
   - Expected: taken.col(Symbol.from("score")).unwrap().values.flat_f64(1) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("id"), values: array_i64([Int64.new(10), Int64.new(20), Int64.new(30)]), dtype: DType.I64, missing: [Bool.new(false), Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]))
]).unwrap()
val taken = df.take_rows(array_i64([Int64.new(2), Int64.new(0)])).unwrap()
expect(taken.num_rows()).to_equal(Index.new(2))
expect(taken.col(Symbol.from("id")).unwrap().values.flat_i64(0)).to_equal(Int64.new(30))
expect(taken.col(Symbol.from("score")).unwrap().values.flat_f64(1)).to_equal(Float64.new(1.0))
```

</details>

#### returns an error for invalid take indices

1. SeriesErased F64Series
2. ]) unwrap
   - Expected: df.take_rows(array_i64([Int64.new(2)])).is_err() is true
   - Expected: df.take_rows(array([Float64.new(0.0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.0)]))
]).unwrap()
expect(df.take_rows(array_i64([Int64.new(2)])).is_err()).to_equal(true)
expect(df.take_rows(array([Float64.new(0.0)])).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
