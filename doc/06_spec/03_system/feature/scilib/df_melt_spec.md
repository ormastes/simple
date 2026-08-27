# DataFrame Melt Numeric Specification

> Validates the constrained numeric wide-to-long reshape. The variable column is

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the constrained numeric wide-to-long reshape. The variable column is
an Int64 ordinal for the selected value column; text/object dtype and
multi-index behavior are intentionally out of scope.

## Scenarios

### DataFrame melt_numeric

#### reshapes numeric value columns to long form with an Int64 variable ordinal

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reshapes numeric value columns to long form with an Int64 variable ordinal
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

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reshapes numeric value columns to long form with an Int64 variable ordinal")
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

- preserves value missing masks
   - Expected: out.col(Symbol.from("value")).unwrap().is_missing(Index.new(0)).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves value missing masks")
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

- returns errors for missing columns, empty value set, and duplicate output names
   - Expected: df.melt_numeric(Symbol.from("id"), [], Symbol.from("variable"), Symbol.from("value")).is_err() is true
   - Expected: df.melt_numeric(Symbol.from("missing"), [Symbol.from("jan")], Symbol.from("variable"), Symbol.from("value")).is_err() is true
   - Expected: df.melt_numeric(Symbol.from("id"), [Symbol.from("missing")], Symbol.from("variable"), Symbol.from("value")).is_err() is true
   - Expected: df.melt_numeric(Symbol.from("id"), [Symbol.from("jan")], Symbol.from("id"), Symbol.from("value")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns errors for missing columns, empty value set, and duplicate output names")
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

- **Plan:** `doc/03_plan/science_math_dataframe_compatibility_manifest.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SCILIB-D-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f4fac8cb49889a5b140b44a354def60ee13218462b1c839fcab8d5d90bf7f27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f4fac8cb49889a5b140b44a354def60ee13218462b1c839fcab8d5d90bf7f27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f4fac8cb49889a5b140b44a354def60ee13218462b1c839fcab8d5d90bf7f27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/scilib/df_melt_spec.spl
mirror: doc/06_spec/03_system/feature/scilib/df_melt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/scilib/df_melt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/scilib/df_melt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/scilib/df_melt_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reshapes numeric value columns to long form with an Int64 variable ordinal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/df_melt_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves value missing masks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/df_melt_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for missing columns, empty value set, and duplicate output names' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
