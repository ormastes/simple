# DataFrame Head And Tail Specification

> Validates row inspection helpers using the same row-gather path as

<!-- sdn-diagram:id=df_head_tail_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_head_tail_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_head_tail_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_head_tail_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Head And Tail Specification

Validates row inspection helpers using the same row-gather path as

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-18, T-DF-19, science-math-lib-set-pandas-core-head-tail |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Source | `test/03_system/feature/scilib/df_head_tail_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates row inspection helpers using the same row-gather path as
`sort_values`.

## Scenarios

### DataFrame head and tail

#### head returns the first n rows across all columns

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
5. ]) unwrap
   - Expected: h.num_rows() equals `Index.new(2)`
   - Expected: h.col(Symbol.from("price")).unwrap().get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: h.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(20)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
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
val h = df.head(Index.new(2)).unwrap()
expect(h.num_rows()).to_equal(Index.new(2))
expect(h.col(Symbol.from("price")).unwrap().get(Index.new(1))).to_equal(Float64.new(2.0))
expect(h.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(20))
```

</details>

#### tail returns the last n rows across all columns

1. name: Symbol from
2. values: [Float64 new
3. name: Symbol from
4. values: [Int64 new
5. ]) unwrap
   - Expected: t.num_rows() equals `Index.new(2)`
   - Expected: t.col(Symbol.from("price")).unwrap().get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: t.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
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
val t = df.tail(Index.new(2)).unwrap()
expect(t.num_rows()).to_equal(Index.new(2))
expect(t.col(Symbol.from("price")).unwrap().get(Index.new(0))).to_equal(Float64.new(2.0))
expect(t.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(30))
```

</details>

#### clamps counts larger than the frame length

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
   - Expected: df.head(Index.new(99)).unwrap().num_rows() equals `Index.new(2)`
   - Expected: df.tail(Index.new(99)).unwrap().num_rows() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
expect(df.head(Index.new(99)).unwrap().num_rows()).to_equal(Index.new(2))
expect(df.tail(Index.new(99)).unwrap().num_rows()).to_equal(Index.new(2))
```

</details>

#### returns ShapeMismatch for negative counts

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
   - Expected: df.head(Index.new(-1)).is_err() is true
   - Expected: df.tail(Index.new(-1)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0)]
    )),
]).unwrap()
expect(df.head(Index.new(-1)).is_err()).to_equal(true)
expect(df.tail(Index.new(-1)).is_err()).to_equal(true)
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

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)


</details>
