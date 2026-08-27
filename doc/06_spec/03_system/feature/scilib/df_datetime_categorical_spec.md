# DataFrame Datetime and Categorical Compatibility Specification

> Validates explicit datetime ingestion and first-seen categorical label

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Manifest:** doc/03_plan/science_math_dataframe_compatibility_manifest.md

Validates explicit datetime ingestion and first-seen categorical label
encoding without adding object dtype or math-block semantics.

## Scenarios

### DataFrame datetime-lite ingestion

#### parses ISO dates to Int64 day offsets from 1970-01-01

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses ISO dates to Int64 day offsets from 1970-01-01
   - Expected: parsed.dtype equals `DType.I64`
   - Expected: parsed.values.flat_i64(0) equals `Int64.new(-1)`
   - Expected: parsed.values.flat_i64(1) equals `Int64.new(0)`
   - Expected: parsed.values.flat_i64(2) equals `Int64.new(1)`
   - Expected: parsed.values.flat_i64(3) equals `Int64.new(18322)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses ISO dates to Int64 day offsets from 1970-01-01")
val parsed = iso_date_series(Symbol.from("date"), ["1969-12-31", "1970-01-01", "1970-01-02", "2020-03-01"]).unwrap()
expect(parsed.dtype).to_equal(DType.I64)
expect(parsed.values.flat_i64(0)).to_equal(Int64.new(-1))
expect(parsed.values.flat_i64(1)).to_equal(Int64.new(0))
expect(parsed.values.flat_i64(2)).to_equal(Int64.new(1))
expect(parsed.values.flat_i64(3)).to_equal(Int64.new(18322))
```

</details>

#### returns parse errors for invalid dates

- returns parse errors for invalid dates
   - Expected: parse_iso_date_days("2020-02-30").is_err() is true
   - Expected: parse_iso_date_days("2020/02/29").is_err() is true
   - Expected: parse_iso_date_days("not-a-date").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns parse errors for invalid dates")
expect(parse_iso_date_days("2020-02-30").is_err()).to_equal(true)
expect(parse_iso_date_days("2020/02/29").is_err()).to_equal(true)
expect(parse_iso_date_days("not-a-date").is_err()).to_equal(true)
```

</details>

### DataFrame categorical-lite encoding

#### encodes labels as first-seen Int64 codes with a label table

- encodes labels as first-seen Int64 codes with a label table
   - Expected: encoded.series.dtype equals `DType.I64`
   - Expected: encoded.series.values.flat_i64(0) equals `Int64.new(0)`
   - Expected: encoded.series.values.flat_i64(1) equals `Int64.new(1)`
   - Expected: encoded.series.values.flat_i64(2) equals `Int64.new(0)`
   - Expected: encoded.labels.len() equals `2`
   - Expected: encoded.labels[0] equals `Symbol.from("red")`
   - Expected: encoded.labels[1] equals `Symbol.from("blue")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encodes labels as first-seen Int64 codes with a label table")
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

- can be assigned to a DataFrame without changing math-block boundaries
   - Expected: df.col(Symbol.from("segment")).unwrap().dtype equals `DType.I64`
   - Expected: df.col(Symbol.from("value")).unwrap().get(Index.new(1)) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can be assigned to a DataFrame without changing math-block boundaries")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SCILIB-D-001`
- `REQ-SCILIB-D-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f42495ce18ac1c1fdab591818a87e1099a89bc487e4006642cd2277370bf483`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f42495ce18ac1c1fdab591818a87e1099a89bc487e4006642cd2277370bf483`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f42495ce18ac1c1fdab591818a87e1099a89bc487e4006642cd2277370bf483`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/feature/scilib/df_datetime_categorical_spec.spl
mirror: doc/06_spec/03_system/feature/scilib/df_datetime_categorical_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=95 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/scilib/df_datetime_categorical_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/scilib/df_datetime_categorical_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/scilib/df_datetime_categorical_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/scilib/df_datetime_categorical_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses ISO dates to Int64 day offsets from 1970-01-01' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/df_datetime_categorical_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns parse errors for invalid dates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/df_datetime_categorical_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes labels as first-seen Int64 codes with a label table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/df_datetime_categorical_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be assigned to a DataFrame without changing math-block boundaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
