# DataFrame Value Counts / Unique / Nunique Specification

> Validates Series.unique_f64, unique_i64, nunique, and value_counts.

<!-- sdn-diagram:id=df_value_counts_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_value_counts_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_value_counts_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_value_counts_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Value Counts / Unique / Nunique Specification

Validates Series.unique_f64, unique_i64, nunique, and value_counts.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-32, science-math-lib-set-pandas-core-value-counts |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_value_counts_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates Series.unique_f64, unique_i64, nunique, and value_counts.

## Scenarios

### Series unique_i64

#### returns deduplicated Int64 values in order of first appearance

1. Symbol from
2. [Int64 new
3. [Bool new
   - Expected: u.len() equals `Index.new(3)`
   - Expected: u.values.flat_i64(0) equals `Int64.new(3)`
   - Expected: u.values.flat_i64(1) equals `Int64.new(1)`
   - Expected: u.values.flat_i64(2) equals `Int64.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = Series.from_i64_masked(
    Symbol.from("group"),
    [Int64.new(3), Int64.new(1), Int64.new(3), Int64.new(2), Int64.new(1)],
    [Bool.new(false), Bool.new(false), Bool.new(false), Bool.new(false), Bool.new(false)]
)
val s = ms.unwrap()
val u = s.unique_i64()
expect(u.len()).to_equal(Index.new(3))
expect(u.values.flat_i64(0)).to_equal(Int64.new(3))
expect(u.values.flat_i64(1)).to_equal(Int64.new(1))
expect(u.values.flat_i64(2)).to_equal(Int64.new(2))
```

</details>

#### returns single-element series for constant column

1. Symbol from
2. [Int64 new
3. [Bool new
   - Expected: u.len() equals `Index.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = Series.from_i64_masked(
    Symbol.from("c"),
    [Int64.new(7), Int64.new(7), Int64.new(7)],
    [Bool.new(false), Bool.new(false), Bool.new(false)]
)
val s = ms.unwrap()
val u = s.unique_i64()
expect(u.len()).to_equal(Index.new(1))
```

</details>

### Series nunique

#### returns count of distinct non-missing values for I64 series

1. name: Symbol from
2. values: [Float64 new
   - Expected: s.nunique() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("x"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0), Float64.new(3.0)]
)
expect(s.nunique()).to_equal(Index.new(3))
```

</details>

#### returns 1 for constant series

1. name: Symbol from
2. values: [Float64 new
   - Expected: s.nunique() equals `Index.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("k"),
    values: [Float64.new(5.0), Float64.new(5.0)]
)
expect(s.nunique()).to_equal(Index.new(1))
```

</details>

#### returns 0 for empty series

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty: [Float64] = []
val s = Series.from_values(name: Symbol.from("empty"), values: empty)
expect(s.nunique()).to_equal(Index.new(0))
```

</details>

### value_counts

#### returns a two-column DataFrame with value and count columns

1. name: Symbol from
2. values: [Float64 new
   - Expected: vc.num_cols() equals `Index.new(2)`
   - Expected: vc.num_rows() equals `Index.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("color"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0), Float64.new(3.0), Float64.new(2.0), Float64.new(2.0)]
)
val vc = value_counts(s)
expect(vc.num_cols()).to_equal(Index.new(2))
expect(vc.num_rows()).to_equal(Index.new(3))
```

</details>

#### count column is named 'count'

1. name: Symbol from
2. values: [Float64 new
   - Expected: schema[1] equals `Symbol.from("count")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("grp"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0)]
)
val vc = value_counts(s)
val schema = vc.columns()
expect(schema[1]).to_equal(Symbol.from("count"))
```

</details>

#### count values are correct

1. name: Symbol from
2. values: [Float64 new
   - Expected: counts.get(Index.new(0)) equals `Int64.new(3)`
   - Expected: counts.get(Index.new(1)) equals `Int64.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("g"),
    values: [Float64.new(1.0), Float64.new(2.0), Float64.new(1.0), Float64.new(1.0)]
)
val vc = value_counts(s)
val counts = vc.col(Symbol.from("count")).unwrap()
expect(counts.get(Index.new(0))).to_equal(Int64.new(3))
expect(counts.get(Index.new(1))).to_equal(Int64.new(1))
```

</details>

#### ignores missing values in count

1. Symbol from
2. [Float64 new
3. [Bool new
   - Expected: vc.num_rows() equals `Index.new(1)`
   - Expected: counts.get(Index.new(0)) equals `Int64.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_f64_masked(
    Symbol.from("v"),
    [Float64.new(1.0), Float64.new(0.0), Float64.new(1.0)],
    [Bool.new(false), Bool.new(true), Bool.new(false)]
).unwrap()
val vc = value_counts(s)
expect(vc.num_rows()).to_equal(Index.new(1))
val counts = vc.col(Symbol.from("count")).unwrap()
expect(counts.get(Index.new(0))).to_equal(Int64.new(2))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
