# DataFrame Melt Numeric Specification

> Validates the constrained numeric wide-to-long reshape. The variable column is

<!-- sdn-diagram:id=df_melt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_melt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_melt_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_melt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Melt Numeric Specification

Validates the constrained numeric wide-to-long reshape. The variable column is

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-D-002, science-math-lib-set-dataframe-reshape-lite |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/science_math_dataframe_compatibility_manifest.md |
| Source | `test/03_system/feature/scilib/df_melt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the constrained numeric wide-to-long reshape. The variable column is
an Int64 ordinal for the selected value column; text/object dtype and
multi-index behavior are intentionally out of scope.

## Scenarios

### DataFrame melt_numeric

#### reshapes numeric value columns to long form with an Int64 variable ordinal

1. SeriesErased I64Series
2. SeriesErased F64Series
3. SeriesErased I64Series
4. ]) unwrap
5. Symbol from
6. [Symbol from
7. Symbol from
8. Symbol from
   - Expected: out.num_rows() equals `Index.new(4)`
   - Expected: out.num_cols() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(0)) equals `Int64.new(1)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(1)) equals `Int64.new(1)`
   - Expected: out.col(Symbol.from("variable")).unwrap().get(Index.new(0)) equals `Int64.new(0)`
   - Expected: out.col(Symbol.from("variable")).unwrap().get(Index.new(1)) equals `Int64.new(1)`
   - Expected: out.col(Symbol.from("value")).unwrap().get(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: out.col(Symbol.from("value")).unwrap().get(Index.new(1)) equals `Float64.new(30.0)`
   - Expected: out.col(Symbol.from("value")).unwrap().get(Index.new(3)) equals `Float64.new(40.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("jan"), [Float64.new(10.0), Float64.new(20.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("feb"), [Int64.new(30), Int64.new(40)])),
]).unwrap()
val out = df.melt_numeric(
    Symbol.from("id"),
    [Symbol.from("jan"), Symbol.from("feb")],
    Symbol.from("variable"),
    Symbol.from("value")
).unwrap()
expect(out.num_rows()).to_equal(Index.new(4))
expect(out.num_cols()).to_equal(Index.new(3))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(0))).to_equal(Int64.new(1))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(1))).to_equal(Int64.new(1))
expect(out.col(Symbol.from("variable")).unwrap().get(Index.new(0))).to_equal(Int64.new(0))
expect(out.col(Symbol.from("variable")).unwrap().get(Index.new(1))).to_equal(Int64.new(1))
expect(out.col(Symbol.from("value")).unwrap().get(Index.new(0))).to_equal(Float64.new(10.0))
expect(out.col(Symbol.from("value")).unwrap().get(Index.new(1))).to_equal(Float64.new(30.0))
expect(out.col(Symbol.from("value")).unwrap().get(Index.new(3))).to_equal(Float64.new(40.0))
```

</details>

#### preserves value missing masks

1. SeriesErased I64Series
2. Symbol from
3. [Float64 new
4. [Bool new
5. ]) unwrap
6. Symbol from
7. [Symbol from
8. Symbol from
9. Symbol from
   - Expected: out.col(Symbol.from("value")).unwrap().is_missing(Index.new(0)).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.F64Series(Series.from_f64_masked(
        Symbol.from("jan"),
        [Float64.new(0.0)],
        [Bool.new(true)]
    ).unwrap()),
]).unwrap()
val out = melt_numeric(
    df,
    Symbol.from("id"),
    [Symbol.from("jan")],
    Symbol.from("variable"),
    Symbol.from("value")
).unwrap()
expect(out.col(Symbol.from("value")).unwrap().is_missing(Index.new(0)).unwrap()).to_equal(true)
```

</details>

#### returns errors for missing columns, empty value set, and duplicate output names

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: df.melt_numeric(Symbol.from("id"), [], Symbol.from("variable"), Symbol.from("value")).is_err() is true
   - Expected: df.melt_numeric(Symbol.from("missing"), [Symbol.from("jan")], Symbol.from("variable"), Symbol.from("value")).is_err() is true
   - Expected: df.melt_numeric(Symbol.from("id"), [Symbol.from("missing")], Symbol.from("variable"), Symbol.from("value")).is_err() is true
   - Expected: df.melt_numeric(Symbol.from("id"), [Symbol.from("jan")], Symbol.from("id"), Symbol.from("value")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("jan"), [Float64.new(10.0)])),
]).unwrap()
expect(df.melt_numeric(Symbol.from("id"), [], Symbol.from("variable"), Symbol.from("value")).is_err()).to_equal(true)
expect(df.melt_numeric(Symbol.from("missing"), [Symbol.from("jan")], Symbol.from("variable"), Symbol.from("value")).is_err()).to_equal(true)
expect(df.melt_numeric(Symbol.from("id"), [Symbol.from("missing")], Symbol.from("variable"), Symbol.from("value")).is_err()).to_equal(true)
expect(df.melt_numeric(Symbol.from("id"), [Symbol.from("jan")], Symbol.from("id"), Symbol.from("value")).is_err()).to_equal(true)
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
