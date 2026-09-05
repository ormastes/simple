# DataFrame Missing Values Specification

> Validates is_na, fill_na, drop_na on Series and DataFrame.

<!-- sdn-diagram:id=df_missing_values_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_missing_values_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_missing_values_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_missing_values_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Missing Values Specification

Validates is_na, fill_na, drop_na on Series and DataFrame.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-16, T-DF-17, science-math-lib-set-pandas-core-missing |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_missing_values_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates is_na, fill_na, drop_na on Series and DataFrame.

## Scenarios

### Series is_na

#### returns Bool series marking missing positions

1. Symbol from
2. [Float64 new
3. [Bool new
4. var na2 = s is na
   - Expected: na2.len() equals `Index.new(3)`
5. var na3 = s is na
   - Expected: na3.values.flat_bool(0) equals `Bool.new(false)`
6. var na4 = s is na
   - Expected: na4.values.flat_bool(1) equals `Bool.new(true)`
7. var na5 = s is na
   - Expected: na5.values.flat_bool(2) equals `Bool.new(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val masked = Series.from_f64_masked(
    Symbol.from("x"),
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Bool.new(false), Bool.new(true), Bool.new(false)]
)
val s = masked.unwrap()
var na2 = s.is_na()
expect(na2.len()).to_equal(Index.new(3))
# verify via flat_bool: position 1 is missing, others are not
var na3 = s.is_na()
expect(na3.values.flat_bool(0)).to_equal(Bool.new(false))
var na4 = s.is_na()
expect(na4.values.flat_bool(1)).to_equal(Bool.new(true))
var na5 = s.is_na()
expect(na5.values.flat_bool(2)).to_equal(Bool.new(false))
```

</details>

#### returns all-false Bool series when no values are missing

1. name: Symbol from
2. values: [Float64 new
3. var na = s is na
   - Expected: na.values.flat_bool(0) equals `Bool.new(false)`
4. var na2 = s is na
   - Expected: na2.values.flat_bool(1) equals `Bool.new(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_values(
    name: Symbol.from("y"),
    values: [Float64.new(1.0), Float64.new(2.0)]
)
var na = s.is_na()
expect(na.values.flat_bool(0)).to_equal(Bool.new(false))
var na2 = s.is_na()
expect(na2.values.flat_bool(1)).to_equal(Bool.new(false))
```

</details>

### Series fill_na

#### replaces missing Float64 values with fill value

1. Symbol from
2. [Float64 new
3. [Bool new
   - Expected: filled.get(Index.new(1)) equals `Float64.new(99.0)`
   - Expected: filled.is_missing(Index.new(1)).unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_f64_masked(
    Symbol.from("x"),
    [Float64.new(1.0), Float64.new(0.0), Float64.new(3.0)],
    [Bool.new(false), Bool.new(true), Bool.new(false)]
).unwrap()
val filled = s.fill_na(Float64.new(99.0))
expect(filled.get(Index.new(1))).to_equal(Float64.new(99.0))
expect(filled.is_missing(Index.new(1)).unwrap()).to_equal(false)
```

</details>

#### leaves non-missing values unchanged

1. Symbol from
2. [Float64 new
3. [Bool new
   - Expected: filled.get(Index.new(0)) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Series.from_f64_masked(
    Symbol.from("a"),
    [Float64.new(5.0), Float64.new(0.0)],
    [Bool.new(false), Bool.new(true)]
).unwrap()
val filled = s.fill_na(Float64.new(0.0))
expect(filled.get(Index.new(0))).to_equal(Float64.new(5.0))
```

</details>

### DataFrame is_na

#### returns boolean DataFrame with same schema

1. Symbol from
2. [Float64 new
3. [Bool new
4. Symbol from
5. [Int64 new
6. [Bool new
7. SeriesErased F64Series
8. SeriesErased I64Series
9. ]) unwrap
   - Expected: na_df.num_cols() equals `Index.new(2)`
   - Expected: col_a.values.flat_bool(1) equals `Bool.new(true)`
   - Expected: col_b.values.flat_bool(0) equals `Bool.new(false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sa = Series.from_f64_masked(
    Symbol.from("a"),
    [Float64.new(1.0), Float64.new(0.0)],
    [Bool.new(false), Bool.new(true)]
)
val sb = Series.from_i64_masked(
    Symbol.from("b"),
    [Int64.new(10), Int64.new(20)],
    [Bool.new(false), Bool.new(false)]
)
val df = DataFrame.from_columns([
    SeriesErased.F64Series(sa.unwrap()),
    SeriesErased.I64Series(sb.unwrap()),
]).unwrap()
val na_df = df.is_na()
expect(na_df.num_cols()).to_equal(Index.new(2))
val col_a_r = na_df.col(Symbol.from("a"))
val col_a = col_a_r.unwrap()
expect(col_a.values.flat_bool(1)).to_equal(Bool.new(true))
val col_b_r = na_df.col(Symbol.from("b"))
val col_b = col_b_r.unwrap()
expect(col_b.values.flat_bool(0)).to_equal(Bool.new(false))
```

</details>

### DataFrame drop_na

#### Any: drops rows where at least one column is missing

1. Symbol from
2. [Float64 new
3. [Bool new
4. Symbol from
5. [Int64 new
6. [Bool new
7. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("x")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: out.col(Symbol.from("x")).unwrap().get(Index.new(1)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_f64_masked(
        Symbol.from("x"),
        [Float64.new(1.0), Float64.new(0.0), Float64.new(3.0)],
        [Bool.new(false), Bool.new(true), Bool.new(false)]
    ).unwrap()),
    SeriesErased.I64Series(Series.from_i64_masked(
        Symbol.from("y"),
        [Int64.new(10), Int64.new(20), Int64.new(30)],
        [Bool.new(false), Bool.new(false), Bool.new(false)]
    ).unwrap()),
]).unwrap()
val out = df.drop_na(NaHow.Any)
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.col(Symbol.from("x")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
expect(out.col(Symbol.from("x")).unwrap().get(Index.new(1))).to_equal(Float64.new(3.0))
```

</details>

#### All: only drops rows where all columns are missing

1. Symbol from
2. [Float64 new
3. [Bool new
4. Symbol from
5. [Int64 new
6. [Bool new
7. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_f64_masked(
        Symbol.from("x"),
        [Float64.new(1.0), Float64.new(0.0), Float64.new(3.0)],
        [Bool.new(false), Bool.new(true), Bool.new(false)]
    ).unwrap()),
    SeriesErased.I64Series(Series.from_i64_masked(
        Symbol.from("y"),
        [Int64.new(10), Int64.new(0), Int64.new(30)],
        [Bool.new(false), Bool.new(true), Bool.new(false)]
    ).unwrap()),
]).unwrap()
val out = df.drop_na(NaHow.All)
expect(out.num_rows()).to_equal(Index.new(2))
```

</details>

#### Any on frame with no missing values leaves all rows

1. name: Symbol from
2. values: [Float64 new
3. ]) unwrap
   - Expected: out.num_rows() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("a"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
val out = df.drop_na(NaHow.Any)
expect(out.num_rows()).to_equal(Index.new(2))
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


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/scilib_port_df.md](doc/03_plan/agent_tasks/scilib_port_df.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
