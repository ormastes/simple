# DataFrame Sort Values Specification

> Validates ascending `DataFrame.sort_values(by)` over numeric columns using

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Sort Values Specification

Validates ascending `DataFrame.sort_values(by)` over numeric columns using

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-18, T-DF-19, science-math-lib-set-pandas-core-sort-values |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_sort_values_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates ascending `DataFrame.sort_values(by)` over numeric columns using
`NDArray.argsort` and dtype-preserving `NDArray.gather`.

## Scenarios

### DataFrame sort_values

#### sorts rows by a Float64 key and reindexes all columns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sorts rows by a Float64 key and reindexes all columns
   - Expected: sorted.col(Symbol.from("price")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: sorted.col(Symbol.from("price")).unwrap().get(Index.new(2)) equals `Float64.new(3.0)`
   - Expected: sorted.col(Symbol.from("qty")).unwrap().get(Index.new(0)) equals `Int64.new(10)`
   - Expected: sorted.col(Symbol.from("qty")).unwrap().get(Index.new(2)) equals `Int64.new(30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sorts rows by a Float64 key and reindexes all columns")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(3.0), Float64.new(1.0), Float64.new(2.0)]
    )),
    SeriesErased.I64Series(Series.from_values(
        name: Symbol.from("qty"),
        values: [Int64.new(30), Int64.new(10), Int64.new(20)]
    )),
]).unwrap()
val sorted = df.sort_values(Symbol.from("price")).unwrap()
expect(sorted.col(Symbol.from("price")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
expect(sorted.col(Symbol.from("price")).unwrap().get(Index.new(2))).to_equal(Float64.new(3.0))
expect(sorted.col(Symbol.from("qty")).unwrap().get(Index.new(0))).to_equal(Int64.new(10))
expect(sorted.col(Symbol.from("qty")).unwrap().get(Index.new(2))).to_equal(Int64.new(30))
```

</details>

#### sorts rows by an Int64 key

- sorts rows by an Int64 key
   - Expected: sorted.col(Symbol.from("rank")).unwrap().get(Index.new(0)) equals `Int64.new(1)`
   - Expected: sorted.col(Symbol.from("price")).unwrap().get(Index.new(0)) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sorts rows by an Int64 key")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(2.0), Float64.new(3.0), Float64.new(1.0)]
    )),
    SeriesErased.I64Series(Series.from_values(
        name: Symbol.from("rank"),
        values: [Int64.new(2), Int64.new(3), Int64.new(1)]
    )),
]).unwrap()
val sorted = df.sort_values(Symbol.from("rank")).unwrap()
expect(sorted.col(Symbol.from("rank")).unwrap().get(Index.new(0))).to_equal(Int64.new(1))
expect(sorted.col(Symbol.from("price")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.0))
```

</details>

#### returns an error when the sort key is missing

- returns an error when the sort key is missing
   - Expected: df.sort_values(Symbol.from("missing")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error when the sort key is missing")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0)]
    )),
]).unwrap()
expect(df.sort_values(Symbol.from("missing")).is_err()).to_equal(true)
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

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_df.md`
- **Design:** `doc/05_design/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82f3ab27f645e47e733b2ef5f271aea254baf0451965f13511a2e3b9df9c2bdb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82f3ab27f645e47e733b2ef5f271aea254baf0451965f13511a2e3b9df9c2bdb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82f3ab27f645e47e733b2ef5f271aea254baf0451965f13511a2e3b9df9c2bdb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_sort_values_spec.spl
mirror: doc/06_spec/feature/scilib/df_sort_values_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_sort_values_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_sort_values_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_sort_values_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts rows by a Float64 key and reindexes all columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_sort_values_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts rows by an Int64 key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_sort_values_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an error when the sort key is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
