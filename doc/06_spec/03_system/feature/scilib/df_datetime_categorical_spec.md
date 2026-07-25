# DataFrame Datetime and Categorical Compatibility Specification

> Validates explicit datetime ingestion and first-seen categorical label

<!-- sdn-diagram:id=df_datetime_categorical_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=df_datetime_categorical_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

df_datetime_categorical_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=df_datetime_categorical_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Datetime and Categorical Compatibility Specification

Validates explicit datetime ingestion and first-seen categorical label

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-D-001, REQ-SCILIB-D-002, science-math-lib-set-datetime-categorical-lite |
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/scilib/df_datetime_categorical_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

**Manifest:** doc/03_plan/science_math_dataframe_compatibility_manifest.md

Validates explicit datetime ingestion and first-seen categorical label
encoding without adding object dtype or math-block semantics.

## Scenarios

### DataFrame datetime-lite ingestion

#### parses ISO dates to Int64 day offsets from 1970-01-01

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = iso_date_series(Symbol.from("date"), ["1969-12-31", "1970-01-01", "1970-01-02", "2020-03-01"]).unwrap()
expect(parsed.dtype).to_equal(DType.I64)
expect(parsed.values.flat_i64(0)).to_equal(Int64.new(-1))
expect(parsed.values.flat_i64(1)).to_equal(Int64.new(0))
expect(parsed.values.flat_i64(2)).to_equal(Int64.new(1))
expect(parsed.values.flat_i64(3)).to_equal(Int64.new(18322))
```

</details>

#### returns parse errors for invalid dates

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_iso_date_days("2020-02-30").is_err()).to_equal(true)
expect(parse_iso_date_days("2020/02/29").is_err()).to_equal(true)
expect(parse_iso_date_days("not-a-date").is_err()).to_equal(true)
```

</details>

### DataFrame categorical-lite encoding

#### encodes labels as first-seen Int64 codes with a label table

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = categorical_encode(Symbol.from("color"), [Symbol.from("red"), Symbol.from("blue"), Symbol.from("red")])
expect(encoded.series.dtype).to_equal(DType.I64)
expect(encoded.series.values.flat_i64(0)).to_equal(Int64.new(0))
expect(encoded.series.values.flat_i64(1)).to_equal(Int64.new(1))
expect(encoded.series.values.flat_i64(2)).to_equal(Int64.new(0))
expect(encoded.labels.len()).to_equal(2)
expect(encoded.labels[0]).to_equal(Symbol.from("red"))
expect(encoded.labels[1]).to_equal(Symbol.from("blue"))
```

</details>

#### can be assigned to a DataFrame without changing math-block boundaries

1. SeriesErased I64Series
2. SeriesErased F64Series
3. ]) unwrap
   - Expected: df.col(Symbol.from("segment")).unwrap().dtype equals `DType.I64`
   - Expected: df.col(Symbol.from("value")).unwrap().get(Index.new(1)) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val encoded = categorical_encode(Symbol.from("segment"), [Symbol.from("a"), Symbol.from("b")])
val df = DataFrame.from_columns([
    SeriesErased.I64Series(encoded.series),
    SeriesErased.F64Series(Series.from_values(Symbol.from("value"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
expect(df.col(Symbol.from("segment")).unwrap().dtype).to_equal(DType.I64)
expect(df.col(Symbol.from("value")).unwrap().get(Index.new(1))).to_equal(Float64.new(2.0))
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


</details>
