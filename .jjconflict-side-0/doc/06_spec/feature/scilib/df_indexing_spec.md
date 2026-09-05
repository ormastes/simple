# DataFrame Indexing Specification

> Validates row lookup and row selection helpers for pandas-style indexing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Indexing Specification

Validates row lookup and row selection helpers for pandas-style indexing.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-df-indexing-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_indexing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates row lookup and row selection helpers for pandas-style indexing.

## Scenarios

### DataFrame row indexing

#### returns a typed row by position

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a typed row by position
   - Expected: row.len() equals `2`
   - Expected: row[0].key equals `Symbol.from("id")`
   - Expected: row[0].value equals `DfValue.I64(Int64.new(20))`
   - Expected: row[1].key equals `Symbol.from("score")`
   - Expected: row[1].value equals `DfValue.F64(Float64.new(2.5))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a typed row by position")
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("id"), values: array_i64([Int64.new(10), Int64.new(20)]), dtype: DType.I64, missing: [Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.5), Float64.new(2.5)]))
]).unwrap()
val row = df.row(Index.new(1)).unwrap()
expect(row.len()).to_equal(2)
expect(row[0].key).to_equal(Symbol.from("id"))
expect(row[0].value).to_equal(DfValue.I64(Int64.new(20)))
expect(row[1].key).to_equal(Symbol.from("score"))
expect(row[1].value).to_equal(DfValue.F64(Float64.new(2.5)))
```

</details>

#### returns an error for out-of-range row lookup

- returns an error for out-of-range row lookup
   - Expected: df.row(Index.new(-1)).is_err() is true
   - Expected: df.row(Index.new(1)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for out-of-range row lookup")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.0)]))
]).unwrap()
expect(df.row(Index.new(-1)).is_err()).to_equal(true)
expect(df.row(Index.new(1)).is_err()).to_equal(true)
```

</details>

#### takes rows in caller-specified order

- takes rows in caller-specified order
   - Expected: taken.num_rows() equals `Index.new(2)`
   - Expected: taken.col(Symbol.from("id")).unwrap().values.flat_i64(0) equals `Int64.new(30)`
   - Expected: taken.col(Symbol.from("score")).unwrap().values.flat_f64(1) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("takes rows in caller-specified order")
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("id"), values: array_i64([Int64.new(10), Int64.new(20), Int64.new(30)]), dtype: DType.I64, missing: [Bool.new(false), Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]))
]).unwrap()
val taken = df.take_rows(array_i64([Int64.new(2), Int64.new(0)])).unwrap()
expect(taken.num_rows()).to_equal(Index.new(2))
expect(taken.col(Symbol.from("id")).unwrap().values.flat_i64(0)).to_equal(Int64.new(30))
expect(taken.col(Symbol.from("score")).unwrap().values.flat_f64(1)).to_equal(Float64.new(1.0))
```

</details>

#### returns an error for invalid take indices

- returns an error for invalid take indices
   - Expected: df.take_rows(array_i64([Int64.new(2)])).is_err() is true
   - Expected: df.take_rows(array([Float64.new(0.0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for invalid take indices")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(1.0)]))
]).unwrap()
expect(df.take_rows(array_i64([Int64.new(2)])).is_err()).to_equal(true)
expect(df.take_rows(array([Float64.new(0.0)])).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `f26021804e37c2e32e24ed66c74e620ab46110472347eb760eea9c4c6422fdbe`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f26021804e37c2e32e24ed66c74e620ab46110472347eb760eea9c4c6422fdbe`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f26021804e37c2e32e24ed66c74e620ab46110472347eb760eea9c4c6422fdbe`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/scilib/df_indexing_spec.spl
mirror: doc/06_spec/feature/scilib/df_indexing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_indexing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_indexing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_indexing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/scilib/df_indexing_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a typed row by position' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_indexing_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an error for out-of-range row lookup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_indexing_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes rows in caller-specified order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
