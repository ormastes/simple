# DataFrame Sort Values Specification

> Validates ascending `DataFrame.sort_values(by)` over numeric columns using

<!-- sdn-diagram:id=df_sort_values_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_sort_values_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_sort_values_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_sort_values_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Sort Values Specification

Validates ascending `DataFrame.sort_values(by)` over numeric columns using

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-18, T-DF-19, science-math-lib-set-pandas-core-sort-values |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_sort_values_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates ascending `DataFrame.sort_values(by)` over numeric columns using
`NDArray.argsort` and dtype-preserving `NDArray.gather`.

## Scenarios

### DataFrame sort_values

#### sorts rows by a Float64 key and reindexes all columns

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
5. ]) unwrap
   - Expected: sorted.col(Symbol.from("price")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: sorted.col(Symbol.from("price")).unwrap().get(Index.new(2)) equals `Float64.new(3.0)`
   - Expected: sorted.col(Symbol.from("qty")).unwrap().get(Index.new(0)) equals `Int64.new(10)`
   - Expected: sorted.col(Symbol.from("qty")).unwrap().get(Index.new(2)) equals `Int64.new(30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(3.0), Float64.new(1.0), Float64.new(2.0)]
    )),
    SeriesErased.I64Series(Series.from_values(
        name: Symbol.from("qty"),
        values: [Int64.new(30), Int64.new(10), Int64.new(20)]
    )),
]).unwrap()
val sorted = df.sort_values(Symbol.from("price")).unwrap()
expect(sorted.col(Symbol.from("price")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
expect(sorted.col(Symbol.from("price")).unwrap().get(Index.new(2))).to_equal(Float64.new(3.0))
expect(sorted.col(Symbol.from("qty")).unwrap().get(Index.new(0))).to_equal(Int64.new(10))
expect(sorted.col(Symbol.from("qty")).unwrap().get(Index.new(2))).to_equal(Int64.new(30))
```

</details>

#### sorts rows by an Int64 key

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
5. ]) unwrap
   - Expected: sorted.col(Symbol.from("rank")).unwrap().get(Index.new(0)) equals `Int64.new(1)`
   - Expected: sorted.col(Symbol.from("price")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(2.0), Float64.new(3.0), Float64.new(1.0)]
    )),
    SeriesErased.I64Series(Series.from_values(
        name: Symbol.from("rank"),
        values: [Int64.new(2), Int64.new(3), Int64.new(1)]
    )),
]).unwrap()
val sorted = df.sort_values(Symbol.from("rank")).unwrap()
expect(sorted.col(Symbol.from("rank")).unwrap().get(Index.new(0))).to_equal(Int64.new(1))
expect(sorted.col(Symbol.from("price")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
```

</details>

#### returns an error when the sort key is missing

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
   - Expected: df.sort_values(Symbol.from("missing")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0)]
    )),
]).unwrap()
expect(df.sort_values(Symbol.from("missing")).is_err()).to_equal(true)
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
