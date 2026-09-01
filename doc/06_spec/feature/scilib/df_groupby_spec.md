# DataFrame GroupBy Specification

> Validates the first pandas-style groupby aggregation slice over labeled

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame GroupBy Specification

Validates the first pandas-style groupby aggregation slice over labeled

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-df-groupby-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_groupby_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first pandas-style groupby aggregation slice over labeled
`DataFrame` columns.

## Scenarios

### DataFrame groupby aggregations

#### groups by an Int64 key and computes sums

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- groups by an Int64 key and computes sums
   - Expected: grouped.num_rows() equals `Index.new(2)`
   - Expected: grouped.col(Symbol.from("team")).unwrap().values.flat_i64(0) equals `Int64.new(1)`
   - Expected: grouped.col(Symbol.from("points")).unwrap().values.flat_f64(0) equals `Float64.new(17.0)`
   - Expected: grouped.col(Symbol.from("team")).unwrap().values.flat_i64(1) equals `Int64.new(2)`
   - Expected: grouped.col(Symbol.from("points")).unwrap().values.flat_f64(1) equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("groups by an Int64 key and computes sums")
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("team"), values: array_i64([Int64.new(1), Int64.new(2), Int64.new(1)]), dtype: DType.I64, missing: [Bool.new(false), Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("points"), [Float64.new(10.0), Float64.new(5.0), Float64.new(7.0)]))
]).unwrap()
val grouped = df.groupby_sum(Symbol.from("team"), Symbol.from("points")).unwrap()
expect(grouped.num_rows()).to_equal(Index.new(2))
expect(grouped.col(Symbol.from("team")).unwrap().values.flat_i64(0)).to_equal(Int64.new(1))
expect(grouped.col(Symbol.from("points")).unwrap().values.flat_f64(0)).to_equal(Float64.new(17.0))
expect(grouped.col(Symbol.from("team")).unwrap().values.flat_i64(1)).to_equal(Int64.new(2))
expect(grouped.col(Symbol.from("points")).unwrap().values.flat_f64(1)).to_equal(Float64.new(5.0))
```

</details>

#### groups by a Float64 key and computes means

- groups by a Float64 key and computes means
   - Expected: grouped.num_rows() equals `Index.new(2)`
   - Expected: grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(0) equals `Float64.new(1.5)`
   - Expected: grouped.col(Symbol.from("score")).unwrap().values.flat_f64(0) equals `Float64.new(3.0)`
   - Expected: grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(1) equals `Float64.new(2.5)`
   - Expected: grouped.col(Symbol.from("score")).unwrap().values.flat_f64(1) equals `Float64.new(10.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("groups by a Float64 key and computes means")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series(name: Symbol.from("bucket"), values: array([Float64.new(1.5), Float64.new(1.5), Float64.new(2.5)]), dtype: DType.F64, missing: [Bool.new(false), Bool.new(false), Bool.new(false)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(2.0), Float64.new(4.0), Float64.new(10.0)]))
]).unwrap()
val grouped = df.groupby_mean(Symbol.from("bucket"), Symbol.from("score")).unwrap()
expect(grouped.num_rows()).to_equal(Index.new(2))
expect(grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(0)).to_equal(Float64.new(1.5))
expect(grouped.col(Symbol.from("score")).unwrap().values.flat_f64(0)).to_equal(Float64.new(3.0))
expect(grouped.col(Symbol.from("bucket")).unwrap().values.flat_f64(1)).to_equal(Float64.new(2.5))
expect(grouped.col(Symbol.from("score")).unwrap().values.flat_f64(1)).to_equal(Float64.new(10.0))
```

</details>

#### returns errors for missing columns and non-F64 value columns

- returns errors for missing columns and non-F64 value columns
   - Expected: df.groupby_sum(Symbol.from("missing"), Symbol.from("points")).is_err() is true
   - Expected: df.groupby_sum(Symbol.from("team"), Symbol.from("points")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for missing columns and non-F64 value columns")
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series(name: Symbol.from("team"), values: array_i64([Int64.new(1)]), dtype: DType.I64, missing: [Bool.new(false)])),
    SeriesErased.I64Series(Series(name: Symbol.from("points"), values: array_i64([Int64.new(10)]), dtype: DType.I64, missing: [Bool.new(false)]))
]).unwrap()
expect(df.groupby_sum(Symbol.from("missing"), Symbol.from("points")).is_err()).to_equal(true)
expect(df.groupby_sum(Symbol.from("team"), Symbol.from("points")).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `e9f9cba019c039b477137084fd80a6cdedf2ec7e030a1b965f34466a90b8ec96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9f9cba019c039b477137084fd80a6cdedf2ec7e030a1b965f34466a90b8ec96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9f9cba019c039b477137084fd80a6cdedf2ec7e030a1b965f34466a90b8ec96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_groupby_spec.spl
mirror: doc/06_spec/feature/scilib/df_groupby_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_groupby_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_groupby_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_groupby_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups by an Int64 key and computes sums' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_groupby_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'groups by a Float64 key and computes means' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_groupby_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for missing columns and non-F64 value columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
