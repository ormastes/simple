# DataFrame CSV Text Specification

> Validates pure CSV text import/export for simple numeric DataFrames.

<!-- sdn-diagram:id=df_csv_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_csv_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_csv_text_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_csv_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame CSV Text Specification

Validates pure CSV text import/export for simple numeric DataFrames.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-df-csv-text-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/03_system/feature/scilib/df_csv_text_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates pure CSV text import/export for simple numeric DataFrames.

## Scenarios

### DataFrame CSV text I/O

#### parses numeric CSV text into F64 columns

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = from_csv_text("x,y\n1.5,2.5\n3.0,4.0").unwrap()
expect(df.num_rows()).to_equal(Index.new(2))
expect(df.num_cols()).to_equal(Index.new(2))
expect(df.col(Symbol.from("x")).unwrap().values.flat_f64(0)).to_equal(Float64.new(1.5))
expect(df.col(Symbol.from("y")).unwrap().values.flat_f64(1)).to_equal(Float64.new(4.0))
```

</details>

#### infers integer CSV columns as I64

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = from_csv_text("id,score\n1,10.5\n2,20.25").unwrap()
val id = df.col(Symbol.from("id")).unwrap()
val score = df.col(Symbol.from("score")).unwrap()
expect(id.dtype).to_equal(DType.I64)
expect(score.dtype).to_equal(DType.F64)
expect(id.values.flat_i64(1)).to_equal(Int64.new(2))
expect(score.values.flat_f64(0)).to_equal(Float64.new(10.5))
```

</details>

#### exports a DataFrame to CSV text and parses it back

1. SeriesErased F64Series
2. SeriesErased I64Series
3. ]) unwrap
   - Expected: csv.starts_with("x,y\n") is true
   - Expected: parsed.col(Symbol.from("x")).unwrap().values.flat_f64(1) equals `Float64.new(3.0)`
   - Expected: parsed.col(Symbol.from("y")).unwrap().dtype equals `DType.I64`
   - Expected: parsed.col(Symbol.from("y")).unwrap().values.flat_i64(1) equals `Int64.new(4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series(name: Symbol.from("x"), values: array([Float64.new(1.0), Float64.new(3.0)]), dtype: DType.F64, missing: [Bool.new(false), Bool.new(false)])),
    SeriesErased.I64Series(Series(name: Symbol.from("y"), values: array_i64([Int64.new(2), Int64.new(4)]), dtype: DType.I64, missing: [Bool.new(false), Bool.new(false)]))
]).unwrap()
val csv = df.to_csv_text().unwrap()
expect(csv.starts_with("x,y\n")).to_equal(true)
val parsed = from_csv_text(csv).unwrap()
expect(parsed.col(Symbol.from("x")).unwrap().values.flat_f64(1)).to_equal(Float64.new(3.0))
expect(parsed.col(Symbol.from("y")).unwrap().dtype).to_equal(DType.I64)
expect(parsed.col(Symbol.from("y")).unwrap().values.flat_i64(1)).to_equal(Int64.new(4))
```

</details>

#### round-trips blank CSV cells as missing values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val df = from_csv_text("x,y\n1.0,\n,4.0").unwrap()
expect(df.col(Symbol.from("y")).unwrap().is_missing(Index.new(0)).unwrap()).to_equal(true)
expect(df.col(Symbol.from("x")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(true)
val csv = df.to_csv_text().unwrap()
expect(csv).to_contain("1.0,")
expect(csv).to_contain(",4.0")
```

</details>

#### returns errors for malformed CSV

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(from_csv_text("").is_err()).to_equal(true)
expect(from_csv_text("x,y\n1.0").is_err()).to_equal(true)
expect(from_csv_text("x\nnope").is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/science_math_lib_set.md](doc/03_plan/agent_tasks/science_math_lib_set.md)
- **Design:** [doc/05_design/science_math_lib_set.md](doc/05_design/science_math_lib_set.md)


</details>
