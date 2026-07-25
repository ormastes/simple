# DataFrame Column Selection Specification

> Validates multi-column selection as a plain DataFrame method. This stays out

<!-- sdn-diagram:id=df_select_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_select_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_select_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_select_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Column Selection Specification

Validates multi-column selection as a plain DataFrame method. This stays out

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-08, science-math-lib-set-pandas-core-select |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_select_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates multi-column selection as a plain DataFrame method. This stays out
of math blocks by design.

## Scenarios

### DataFrame select

#### returns a new DataFrame with requested columns in requested order

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
5. name: Symbol from
6. values: [Float64 new
7. ]) unwrap
   - Expected: selected.num_rows() equals `Index.new(2)`
   - Expected: selected.num_cols() equals `Index.new(2)`
   - Expected: selected.columns()[0] equals `Symbol.from("c")`
   - Expected: selected.columns()[1] equals `Symbol.from("a")`
   - Expected: selected.col(Symbol.from("c")).unwrap().get(Index.new(1)) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("a"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
    SeriesErased.I64Series(Series.from_values(
        name: Symbol.from("b"),
        values: [Int64.new(10), Int64.new(20)]
    )),
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("c"),
        values: [Float64.new(3.0), Float64.new(4.0)]
    )),
]).unwrap()
val selected = df.select([Symbol.from("c"), Symbol.from("a")]).unwrap()
expect(selected.num_rows()).to_equal(Index.new(2))
expect(selected.num_cols()).to_equal(Index.new(2))
expect(selected.columns()[0]).to_equal(Symbol.from("c"))
expect(selected.columns()[1]).to_equal(Symbol.from("a"))
expect(selected.col(Symbol.from("c")).unwrap().get(Index.new(1))).to_equal(Float64.new(4.0))
```

</details>

#### returns ColumnNotFound when any requested column is missing

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
   - Expected: df.select([Symbol.from("a"), Symbol.from("missing")]).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("a"),
        values: [Float64.new(1.0)]
    )),
]).unwrap()
expect(df.select([Symbol.from("a"), Symbol.from("missing")]).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
