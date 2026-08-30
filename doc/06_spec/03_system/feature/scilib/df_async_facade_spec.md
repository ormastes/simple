# DataFrame Async/NoGC Facade Specification

> Validates the first namespace-consistency slice from the science math lib set:

<!-- sdn-diagram:id=df_async_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_async_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_async_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_async_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Async/NoGC Facade Specification

Validates the first namespace-consistency slice from the science math lib set:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-async-df-facade |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_async_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first namespace-consistency slice from the science math lib set:
`std.nogc_async_mut.df` exposes the same DataFrame seed API as the existing
`std.df` / `std.nogc_sync_mut.df` surface.

## Scenarios

### nogc_async_mut DataFrame facade

#### constructs a DataFrame through the async/nogc namespace

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
   - Expected: df.num_rows() equals `Index.new(2)`
   - Expected: df.num_cols() equals `Index.new(2)`
   - Expected: df.columns()[0] equals `Symbol.from("price")`
   - Expected: df.dtypes().dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val price_col = SeriesErased.F64Series(Series.from_values(
    name: Symbol.from("price"),
    values: [Float64.new(1.0), Float64.new(2.0)]
))
val qty_col = SeriesErased.I64Series(Series.from_values(
    name: Symbol.from("qty"),
    values: [Int64.new(5), Int64.new(8)]
))
val df = DataFrame.from_columns([price_col, qty_col]).unwrap()
expect(df.num_rows()).to_equal(Index.new(2))
expect(df.num_cols()).to_equal(Index.new(2))
expect(df.columns()[0]).to_equal(Symbol.from("price"))
expect(df.dtypes().dtype_at(Index.new(1))).to_equal(DType.I64)
```

</details>

#### uses the same column operation behavior as the sync facade

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
4. Symbol from
5. name: Symbol from
6. values: [Float64 new
   - Expected: df2.column_count() equals `Index.new(2)`
   - Expected: b.get(Index.new(1)) equals `Float64.new(20.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("a"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
val df2 = df.assign(
    Symbol.from("b"),
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("b"),
        values: [Float64.new(10.0), Float64.new(20.0)]
    ))
)
val b = df2.col(Symbol.from("b")).unwrap()
expect(df2.column_count()).to_equal(Index.new(2))
expect(b.get(Index.new(1))).to_equal(Float64.new(20.0))
```

</details>

#### exposes reshape helpers through the async/nogc namespace

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
4. Symbol from
5. [Symbol from
6. Symbol from
7. Symbol from
   - Expected: long.num_rows() equals `Index.new(1)`
   - Expected: long.col(Symbol.from("value")).unwrap().get(Index.new(0)) equals `Float64.new(10.0)`
8. Symbol from
9. Symbol from
10. Symbol from
11. Symbol from
   - Expected: pivoted.num_cols() equals `Index.new(2)`
   - Expected: pivoted.col(Symbol.from("value_0")).unwrap().get(Index.new(0)) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wide = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("jan"), [Float64.new(10.0)])),
]).unwrap()
val long = melt_numeric(
    wide,
    Symbol.from("id"),
    [Symbol.from("jan")],
    Symbol.from("variable"),
    Symbol.from("value")
).unwrap()
expect(long.num_rows()).to_equal(Index.new(1))
expect(long.col(Symbol.from("value")).unwrap().get(Index.new(0))).to_equal(Float64.new(10.0))

val pivoted = pivot_sum(
    long,
    Symbol.from("id"),
    Symbol.from("variable"),
    Symbol.from("value"),
    Symbol.from("value")
).unwrap()
expect(pivoted.num_cols()).to_equal(Index.new(2))
expect(pivoted.col(Symbol.from("value_0")).unwrap().get(Index.new(0))).to_equal(Float64.new(10.0))
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
