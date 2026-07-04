# DataFrame Concat Specification

> Validates strict row and column concatenation for DataFrame seeds.

<!-- sdn-diagram:id=df_concat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_concat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_concat_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_concat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Concat Specification

Validates strict row and column concatenation for DataFrame seeds.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-22, T-DF-23, science-math-lib-set-pandas-core-concat |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Source | `test/03_system/feature/scilib/df_concat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates strict row and column concatenation for DataFrame seeds.

## Scenarios

### DataFrame concat rows

#### appends rows when schemas and dtypes match

1. SeriesErased F64Series
2. SeriesErased I64Series
3. ]) unwrap
4. SeriesErased F64Series
5. SeriesErased I64Series
6. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(3)`
   - Expected: out.num_cols() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("price")).unwrap().get(Index.new(2)) equals `Float64.new(3.0)`
   - Expected: out.col(Symbol.from("qty")).unwrap().get(Index.new(2)) equals `Int64.new(30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0), Float64.new(2.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("qty"), [Int64.new(10), Int64.new(20)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(3.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("qty"), [Int64.new(30)])),
]).unwrap()
val out = concat([left, right], ConcatAxis.Rows).unwrap()
expect(out.num_rows()).to_equal(Index.new(3))
expect(out.num_cols()).to_equal(Index.new(2))
expect(out.col(Symbol.from("price")).unwrap().get(Index.new(2))).to_equal(Float64.new(3.0))
expect(out.col(Symbol.from("qty")).unwrap().get(Index.new(2))).to_equal(Int64.new(30))
```

</details>

#### rejects row concat when schemas differ

1. SeriesErased F64Series
2. ]) unwrap
3. SeriesErased F64Series
4. ]) unwrap
   - Expected: concat([left, right], ConcatAxis.Rows).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("cost"), [Float64.new(1.0)])),
]).unwrap()
expect(concat([left, right], ConcatAxis.Rows).is_err()).to_equal(true)
```

</details>

### DataFrame concat cols

#### appends columns when row counts match

1. SeriesErased F64Series
2. ]) unwrap
3. SeriesErased I64Series
4. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.num_cols() equals `Index.new(2)`
   - Expected: out.columns()[1] equals `Symbol.from("qty")`
   - Expected: out.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(20)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("qty"), [Int64.new(10), Int64.new(20)])),
]).unwrap()
val out = concat([left, right], ConcatAxis.Cols).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.num_cols()).to_equal(Index.new(2))
expect(out.columns()[1]).to_equal(Symbol.from("qty"))
expect(out.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(20))
```

</details>

#### rejects column concat with duplicate names

1. SeriesErased F64Series
2. ]) unwrap
3. SeriesErased F64Series
4. ]) unwrap
   - Expected: concat([left, right], ConcatAxis.Cols).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(2.0)])),
]).unwrap()
expect(concat([left, right], ConcatAxis.Cols).is_err()).to_equal(true)
```

</details>

#### rejects empty frame lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frames: [DataFrame] = []
expect(concat(frames, ConcatAxis.Rows).is_err()).to_equal(true)
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

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)


</details>
