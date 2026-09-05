# DataFrame CSV Text Specification

> Validates pure CSV text import/export for simple numeric DataFrames.

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
| Source | `test/feature/scilib/df_csv_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates pure CSV text import/export for simple numeric DataFrames.

## Scenarios

### DataFrame CSV text I/O

#### parses numeric CSV text into F64 columns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses numeric CSV text into F64 columns
   - Expected: df.num_rows() equals `Index.new(2)`
   - Expected: df.num_cols() equals `Index.new(2)`
   - Expected: df.col(Symbol.from("x")).unwrap().values.flat_f64(0) equals `Float64.new(1.5)`
   - Expected: df.col(Symbol.from("y")).unwrap().values.flat_f64(1) equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses numeric CSV text into F64 columns")
val df = from_csv_text("x,y\n1.5,2.5\n3.0,4.0").unwrap()
expect(df.num_rows()).to_equal(Index.new(2))
expect(df.num_cols()).to_equal(Index.new(2))
expect(df.col(Symbol.from("x")).unwrap().values.flat_f64(0)).to_equal(Float64.new(1.5))
expect(df.col(Symbol.from("y")).unwrap().values.flat_f64(1)).to_equal(Float64.new(4.0))
```

</details>

#### infers integer CSV columns as I64

- infers integer CSV columns as I64
   - Expected: id.dtype equals `DType.I64`
   - Expected: score.dtype equals `DType.F64`
   - Expected: id.values.flat_i64(1) equals `Int64.new(2)`
   - Expected: score.values.flat_f64(0) equals `Float64.new(10.5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("infers integer CSV columns as I64")
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

- exports a DataFrame to CSV text and parses it back
   - Expected: csv.starts_with("x,y\n") is true
   - Expected: parsed.col(Symbol.from("x")).unwrap().values.flat_f64(1) equals `Float64.new(3.0)`
   - Expected: parsed.col(Symbol.from("y")).unwrap().dtype equals `DType.I64`
   - Expected: parsed.col(Symbol.from("y")).unwrap().values.flat_i64(1) equals `Int64.new(4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("exports a DataFrame to CSV text and parses it back")
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

- round-trips blank CSV cells as missing values
   - Expected: df.col(Symbol.from("y")).unwrap().is_missing(Index.new(0)).unwrap() is true
   - Expected: df.col(Symbol.from("x")).unwrap().is_missing(Index.new(1)).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("round-trips blank CSV cells as missing values")
val df = from_csv_text("x,y\n1.0,\n,4.0").unwrap()
expect(df.col(Symbol.from("y")).unwrap().is_missing(Index.new(0)).unwrap()).to_equal(true)
expect(df.col(Symbol.from("x")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(true)
val csv = df.to_csv_text().unwrap()
expect(csv).to_contain("1.0,")
expect(csv).to_contain(",4.0")
```

</details>

#### returns errors for malformed CSV

- returns errors for malformed CSV
   - Expected: from_csv_text("").is_err() is true
   - Expected: from_csv_text("x,y\n1.0").is_err() is true
   - Expected: from_csv_text("x\nnope").is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for malformed CSV")
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

- **Plan:** `doc/03_plan/agent_tasks/science_math_lib_set.md`
- **Design:** `doc/05_design/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4455f0dfe66ce82f33fef89c2ae088fb5f51fe95121322845c6f194ed7ea076e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4455f0dfe66ce82f33fef89c2ae088fb5f51fe95121322845c6f194ed7ea076e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4455f0dfe66ce82f33fef89c2ae088fb5f51fe95121322845c6f194ed7ea076e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_csv_text_spec.spl
mirror: doc/06_spec/feature/scilib/df_csv_text_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_csv_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_csv_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_csv_text_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses numeric CSV text into F64 columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_csv_text_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers integer CSV columns as I64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_csv_text_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports a DataFrame to CSV text and parses it back' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
