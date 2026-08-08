# DataFrame Pivot Sum Specification

> Validates constrained long-to-wide numeric pivoting. The column key is Int64,

<!-- sdn-diagram:id=df_pivot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_pivot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_pivot_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_pivot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Pivot Sum Specification

Validates constrained long-to-wide numeric pivoting. The column key is Int64,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-D-002, science-math-lib-set-dataframe-pivot-lite |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/science_math_dataframe_compatibility_manifest.md |
| Source | `test/03_system/feature/scilib/df_pivot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates constrained long-to-wide numeric pivoting. The column key is Int64,
the value column is Float64, duplicate groups are summed explicitly, and
missing cells remain masked.

## Scenarios

### DataFrame pivot_sum

#### pivots long numeric rows to wide summed columns

1. SeriesErased I64Series
2. SeriesErased I64Series
3. SeriesErased F64Series
4. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.num_cols() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(0)) equals `Int64.new(1)`
   - Expected: out.col(Symbol.from("sales_0")).unwrap().get(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: out.col(Symbol.from("sales_1")).unwrap().get(Index.new(0)) equals `Float64.new(7.0)`
   - Expected: out.col(Symbol.from("sales_0")).unwrap().get(Index.new(1)) equals `Float64.new(20.0)`
   - Expected: out.col(Symbol.from("sales_1")).unwrap().is_missing(Index.new(1)).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(1), Int64.new(1), Int64.new(2)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("month"), [Int64.new(0), Int64.new(1), Int64.new(1), Int64.new(0)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("sales"), [Float64.new(10.0), Float64.new(3.0), Float64.new(4.0), Float64.new(20.0)])),
]).unwrap()
val out = df.pivot_sum(Symbol.from("id"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.num_cols()).to_equal(Index.new(3))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(0))).to_equal(Int64.new(1))
expect(out.col(Symbol.from("sales_0")).unwrap().get(Index.new(0))).to_equal(Float64.new(10.0))
expect(out.col(Symbol.from("sales_1")).unwrap().get(Index.new(0))).to_equal(Float64.new(7.0))
expect(out.col(Symbol.from("sales_0")).unwrap().get(Index.new(1))).to_equal(Float64.new(20.0))
expect(out.col(Symbol.from("sales_1")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(true)
```

</details>

#### supports Float64 index keys

1. SeriesErased F64Series
2. SeriesErased I64Series
3. SeriesErased F64Series
4. ]) unwrap
   - Expected: out.col(Symbol.from("bucket")).unwrap().get(Index.new(0)) equals `Float64.new(1.5)`
   - Expected: out.col(Symbol.from("v_0")).unwrap().get(Index.new(1)) equals `Float64.new(8.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("bucket"), [Float64.new(1.5), Float64.new(2.5)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("slot"), [Int64.new(0), Int64.new(0)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("value"), [Float64.new(2.0), Float64.new(8.0)])),
]).unwrap()
val out = pivot_sum(df, Symbol.from("bucket"), Symbol.from("slot"), Symbol.from("value"), Symbol.from("v")).unwrap()
expect(out.col(Symbol.from("bucket")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.5))
expect(out.col(Symbol.from("v_0")).unwrap().get(Index.new(1))).to_equal(Float64.new(8.0))
```

</details>

#### returns errors for missing columns, duplicate roles, and invalid dtypes

1. SeriesErased I64Series
2. SeriesErased I64Series
3. SeriesErased I64Series
4. ]) unwrap
   - Expected: df.pivot_sum(Symbol.from("missing"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err() is true
   - Expected: df.pivot_sum(Symbol.from("id"), Symbol.from("id"), Symbol.from("sales"), Symbol.from("sales")).is_err() is true
   - Expected: df.pivot_sum(Symbol.from("id"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("month"), [Int64.new(0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("sales"), [Int64.new(10)])),
]).unwrap()
expect(df.pivot_sum(Symbol.from("missing"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err()).to_equal(true)
expect(df.pivot_sum(Symbol.from("id"), Symbol.from("id"), Symbol.from("sales"), Symbol.from("sales")).is_err()).to_equal(true)
expect(df.pivot_sum(Symbol.from("id"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err()).to_equal(true)
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

- **Plan:** [doc/03_plan/science_math_dataframe_compatibility_manifest.md](doc/03_plan/science_math_dataframe_compatibility_manifest.md)


</details>
