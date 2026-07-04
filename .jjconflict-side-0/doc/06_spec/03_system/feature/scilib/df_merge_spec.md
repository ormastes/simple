# DataFrame Merge Specification

> Validates numeric-key merge/join behavior, including missing-value masks for

<!-- sdn-diagram:id=df_merge_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_merge_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_merge_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_merge_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Merge Specification

Validates numeric-key merge/join behavior, including missing-value masks for

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-24, T-DF-25, T-DF-26, science-math-lib-set-pandas-core-inner-merge |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Source | `test/03_system/feature/scilib/df_merge_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates numeric-key merge/join behavior, including missing-value masks for
unmatched rows in left/right/outer joins.

## Scenarios

### DataFrame merge

#### keeps only matching rows and appends right non-key columns

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
4. SeriesErased I64Series
5. SeriesErased F64Series
6. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.num_cols() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(0)) equals `Int64.new(2)`
   - Expected: out.col(Symbol.from("price")).unwrap().get(Index.new(1)) equals `Float64.new(30.0)`
   - Expected: out.col(Symbol.from("discount")).unwrap().get(Index.new(1)) equals `Float64.new(0.3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2), Int64.new(3)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2), Int64.new(3), Int64.new(4)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.2), Float64.new(0.3), Float64.new(0.4)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Inner).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.num_cols()).to_equal(Index.new(3))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(0))).to_equal(Int64.new(2))
expect(out.col(Symbol.from("price")).unwrap().get(Index.new(1))).to_equal(Float64.new(30.0))
expect(out.col(Symbol.from("discount")).unwrap().get(Index.new(1))).to_equal(Float64.new(0.3))
```

</details>

#### supports the DataFrame.join method wrapper

1. SeriesErased I64Series
2. ]) unwrap
3. SeriesErased I64Series
4. SeriesErased F64Series
5. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(1)`
   - Expected: out.col(Symbol.from("score")).unwrap().get(Index.new(0)) equals `Float64.new(9.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(9.0)])),
]).unwrap()
val out = left.join(right, Symbol.from("id"), JoinHow.Inner).unwrap()
expect(out.num_rows()).to_equal(Index.new(1))
expect(out.col(Symbol.from("score")).unwrap().get(Index.new(0))).to_equal(Float64.new(9.0))
```

</details>

#### left join preserves left rows and marks missing right values

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
4. SeriesErased I64Series
5. SeriesErased F64Series
6. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(0)) equals `Int64.new(1)`
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap() is true
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0), Float64.new(20.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.2)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Left).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(0))).to_equal(Int64.new(1))
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap()).to_equal(true)
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(false)
```

</details>

#### right join preserves right rows and fills missing left columns

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
4. SeriesErased I64Series
5. SeriesErased F64Series
6. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(1)) equals `Int64.new(2)`
   - Expected: out.col(Symbol.from("price")).unwrap().is_missing(Index.new(1)).unwrap() is true
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.1), Float64.new(0.2)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Right).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(1))).to_equal(Int64.new(2))
expect(out.col(Symbol.from("price")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(true)
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(false)
```

</details>

#### outer join includes unmatched rows from both sides

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
4. SeriesErased I64Series
5. SeriesErased F64Series
6. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(2)) equals `Int64.new(3)`
   - Expected: out.col(Symbol.from("price")).unwrap().is_missing(Index.new(2)).unwrap() is true
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0), Float64.new(20.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2), Int64.new(3)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.2), Float64.new(0.3)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Outer).unwrap()
expect(out.num_rows()).to_equal(Index.new(3))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(2))).to_equal(Int64.new(3))
expect(out.col(Symbol.from("price")).unwrap().is_missing(Index.new(2)).unwrap()).to_equal(true)
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap()).to_equal(true)
```

</details>

#### returns errors for missing keys

1. SeriesErased I64Series
2. ]) unwrap
3. SeriesErased I64Series
4. ]) unwrap
   - Expected: merge(left, right, Symbol.from("id"), JoinHow.Inner).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("other_id"), [Int64.new(1)])),
]).unwrap()
expect(merge(left, right, Symbol.from("id"), JoinHow.Inner).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)


</details>
