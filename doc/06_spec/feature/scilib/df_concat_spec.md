# DataFrame Concat Specification

> Validates strict row and column concatenation for DataFrame seeds.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Concat Specification

Validates strict row and column concatenation for DataFrame seeds.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-22, T-DF-23, science-math-lib-set-pandas-core-concat |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Source | `test/feature/scilib/df_concat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates strict row and column concatenation for DataFrame seeds.

## Scenarios

### DataFrame concat rows

#### appends rows when schemas and dtypes match

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- appends rows when schemas and dtypes match
   - Expected: out.num_rows() equals `Index.new(3)`
   - Expected: out.num_cols() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("price")).unwrap().get(Index.new(2)) equals `Float64.new(3.0)`
   - Expected: out.col(Symbol.from("qty")).unwrap().get(Index.new(2)) equals `Int64.new(30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("appends rows when schemas and dtypes match")
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0), Float64.new(2.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("qty"), [Int64.new(10), Int64.new(20)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(3.0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("qty"), [Int64.new(30)])),
]).unwrap()
val out = concat([left, right], ConcatAxis.Rows).unwrap()
expect(out.num_rows()).to_equal(Index.new(3))
expect(out.num_cols()).to_equal(Index.new(2))
expect(out.col(Symbol.from("price")).unwrap().get(Index.new(2))).to_equal(Float64.new(3.0))
expect(out.col(Symbol.from("qty")).unwrap().get(Index.new(2))).to_equal(Int64.new(30))
```

</details>

#### rejects row concat when schemas differ

- rejects row concat when schemas differ
   - Expected: concat([left, right], ConcatAxis.Rows).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects row concat when schemas differ")
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("cost"), [Float64.new(1.0)])),
]).unwrap()
expect(concat([left, right], ConcatAxis.Rows).is_err()).to_equal(true)
```

</details>

### DataFrame concat cols

#### appends columns when row counts match

- appends columns when row counts match
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.num_cols() equals `Index.new(2)`
   - Expected: out.columns()[1] equals `Symbol.from("qty")`
   - Expected: out.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(20)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("appends columns when row counts match")
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0), Float64.new(2.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("qty"), [Int64.new(10), Int64.new(20)])),
]).unwrap()
val out = concat([left, right], ConcatAxis.Cols).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.num_cols()).to_equal(Index.new(2))
expect(out.columns()[1]).to_equal(Symbol.from("qty"))
expect(out.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(20))
```

</details>

#### rejects column concat with duplicate names

- rejects column concat with duplicate names
   - Expected: concat([left, right], ConcatAxis.Cols).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects column concat with duplicate names")
val left = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(1.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(2.0)])),
]).unwrap()
expect(concat([left, right], ConcatAxis.Cols).is_err()).to_equal(true)
```

</details>

#### rejects empty frame lists

- rejects empty frame lists
   - Expected: concat(frames, ConcatAxis.Rows).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects empty frame lists")
val frames: [DataFrame] = []
expect(concat(frames, ConcatAxis.Rows).is_err()).to_equal(true)
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

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_df.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8fd51377e6fd5f5e3803b07682a7cac1a6b659653d1b81dad37bd05d7bd55c1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8fd51377e6fd5f5e3803b07682a7cac1a6b659653d1b81dad37bd05d7bd55c1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8fd51377e6fd5f5e3803b07682a7cac1a6b659653d1b81dad37bd05d7bd55c1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_concat_spec.spl
mirror: doc/06_spec/feature/scilib/df_concat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_concat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_concat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_concat_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends rows when schemas and dtypes match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_concat_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects row concat when schemas differ' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_concat_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'appends columns when row counts match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
