# DataFrame Symbol Interning Specification

> Validates PERF-SUGAR-006: DataFrame column-name Symbols keep their text labels

<!-- sdn-diagram:id=df_symbol_intern_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_symbol_intern_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_symbol_intern_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_symbol_intern_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Symbol Interning Specification

Validates PERF-SUGAR-006: DataFrame column-name Symbols keep their text labels

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/df_symbol_intern_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates PERF-SUGAR-006: DataFrame column-name Symbols keep their text labels
while using stable intern ids for repeated name lookups and duplicate checks.

## Scenarios

### DataFrame Symbol intern ids

#### reuses ids for equal text and keeps distinct ids for different text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a1 = Symbol.from("alpha")
val a2 = Symbol.from("alpha")
val b = Symbol.from("beta")
expect(a1.intern_id()).to_equal(a2.intern_id())
expect(a1.intern_id() != b.intern_id()).to_equal(true)
expect(a1.label()).to_equal("alpha")
```

</details>

#### selects with freshly constructed same-text symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selected = _base_df().select([Symbol.from("extra"), Symbol.from("value")]).unwrap()
expect(selected.columns()[0].intern_id()).to_equal(Symbol.from("extra").intern_id())
expect(selected.columns()[1].intern_id()).to_equal(Symbol.from("value").intern_id())
expect(selected.col(Symbol.from("value")).unwrap().get(Index.new(1))).to_equal(Float64.new(20.0))
```

</details>

#### detects duplicate rename targets by intern id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _base_df().rename(Symbol.from("extra"), Symbol.from("value"))
expect(result.is_err()).to_equal(true)
```

</details>

#### groups with freshly constructed same-text symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val grouped = _base_df().groupby_sum(Symbol.from("id"), Symbol.from("value")).unwrap()
expect(grouped.col(Symbol.from("id")).unwrap().values.flat_i64(0)).to_equal(Int64.new(1))
expect(grouped.col(Symbol.from("value")).unwrap().values.flat_f64(0)).to_equal(Float64.new(15.0))
```

</details>

#### concat rows accepts independently interned same schemas

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = _base_df().select([Symbol.from("id"), Symbol.from("value")]).unwrap()
val right = _base_df().select([Symbol.from("id"), Symbol.from("value")]).unwrap()
val out = concat([left, right], ConcatAxis.Rows).unwrap()
expect(out.num_rows()).to_equal(Index.new(6))
```

</details>

#### concat columns rejects duplicate fresh same-text names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = _base_df().select([Symbol.from("id")]).unwrap()
val right = _base_df().select([Symbol.from("id")]).unwrap()
expect(concat([left, right], ConcatAxis.Cols).is_err()).to_equal(true)
```

</details>

#### merge skips the right join key by intern id

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
4. SeriesErased I64Series
5. SeriesErased F64Series
6. ]) unwrap
   - Expected: out.num_cols() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("right_value")).unwrap().get(Index.new(0)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("left_value"), [Float64.new(10.0), Float64.new(20.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("right_value"), [Float64.new(3.0)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Inner).unwrap()
expect(out.num_cols()).to_equal(Index.new(3))
expect(out.col(Symbol.from("right_value")).unwrap().get(Index.new(0))).to_equal(Float64.new(3.0))
```

</details>

#### melt and pivot reject duplicate symbol arguments by intern id

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = _base_df()
expect(df.melt_numeric(Symbol.from("id"), [Symbol.from("value")], Symbol.from("id"), Symbol.from("melt_value")).is_err()).to_equal(true)
expect(df.pivot_sum(Symbol.from("id"), Symbol.from("id"), Symbol.from("value"), Symbol.from("value")).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
