# DataFrame Pivot Sum Specification

> Validates constrained long-to-wide numeric pivoting. The column key is Int64,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Pivot Sum Specification

Validates constrained long-to-wide numeric pivoting. The column key is Int64,

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-SCILIB-D-002, science-math-lib-set-dataframe-pivot-lite |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/science_math_dataframe_compatibility_manifest.md |
| Source | `test/03_system/feature/scilib/df_pivot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates constrained long-to-wide numeric pivoting. The column key is Int64,
the value column is Float64, duplicate groups are summed explicitly, and
missing cells remain masked.

## Scenarios

### DataFrame pivot_sum

#### pivots long numeric rows to wide summed columns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- pivots long numeric rows to wide summed columns
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.num_cols() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(0)) equals `Int64.new(1)`
   - Expected: out.col(Symbol.from("sales_0")).unwrap().get(Index.new(0)) equals `Float64.new(10.0)`
   - Expected: out.col(Symbol.from("sales_1")).unwrap().get(Index.new(0)) equals `Float64.new(7.0)`
   - Expected: out.col(Symbol.from("sales_0")).unwrap().get(Index.new(1)) equals `Float64.new(20.0)`
   - Expected: out.col(Symbol.from("sales_1")).unwrap().is_missing(Index.new(1)).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pivots long numeric rows to wide summed columns")
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(1), Int64.new(1), Int64.new(2)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("month"), [Int64.new(0), Int64.new(1), Int64.new(1), Int64.new(0)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("sales"), [Float64.new(10.0), Float64.new(3.0), Float64.new(4.0), Float64.new(20.0)])),
]).unwrap()
val out = df.pivot_sum(Symbol.from("id"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.num_cols()).to_equal(Index.new(3))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(0))).to_equal(Int64.new(1))
expect(out.col(Symbol.from("sales_0")).unwrap().get(Index.new(0))).to_equal(Float64.new(10.0))
expect(out.col(Symbol.from("sales_1")).unwrap().get(Index.new(0))).to_equal(Float64.new(7.0))
expect(out.col(Symbol.from("sales_0")).unwrap().get(Index.new(1))).to_equal(Float64.new(20.0))
expect(out.col(Symbol.from("sales_1")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(true)
```

</details>

#### supports Float64 index keys

- supports Float64 index keys
   - Expected: out.col(Symbol.from("bucket")).unwrap().get(Index.new(0)) equals `Float64.new(1.5)`
   - Expected: out.col(Symbol.from("v_0")).unwrap().get(Index.new(1)) equals `Float64.new(8.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports Float64 index keys")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(Symbol.from("bucket"), [Float64.new(1.5), Float64.new(2.5)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("slot"), [Int64.new(0), Int64.new(0)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("value"), [Float64.new(2.0), Float64.new(8.0)])),
]).unwrap()
val out = pivot_sum(df, Symbol.from("bucket"), Symbol.from("slot"), Symbol.from("value"), Symbol.from("v")).unwrap()
expect(out.col(Symbol.from("bucket")).unwrap().get(Index.new(0))).to_equal(Float64.new(1.5))
expect(out.col(Symbol.from("v_0")).unwrap().get(Index.new(1))).to_equal(Float64.new(8.0))
```

</details>

#### returns errors for missing columns, duplicate roles, and invalid dtypes

- returns errors for missing columns, duplicate roles, and invalid dtypes
   - Expected: df.pivot_sum(Symbol.from("missing"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err() is true
   - Expected: df.pivot_sum(Symbol.from("id"), Symbol.from("id"), Symbol.from("sales"), Symbol.from("sales")).is_err() is true
   - Expected: df.pivot_sum(Symbol.from("id"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns errors for missing columns, duplicate roles, and invalid dtypes")
val df = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("month"), [Int64.new(0)])),
    SeriesErased.I64Series(Series.from_values(Symbol.from("sales"), [Int64.new(10)])),
]).unwrap()
expect(df.pivot_sum(Symbol.from("missing"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err()).to_equal(true)
expect(df.pivot_sum(Symbol.from("id"), Symbol.from("id"), Symbol.from("sales"), Symbol.from("sales")).is_err()).to_equal(true)
expect(df.pivot_sum(Symbol.from("id"), Symbol.from("month"), Symbol.from("sales"), Symbol.from("sales")).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `63b69436caf0f294a3808c3d067ba6eda40eb795cb9449c5387b62781a711174`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `63b69436caf0f294a3808c3d067ba6eda40eb795cb9449c5387b62781a711174`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `63b69436caf0f294a3808c3d067ba6eda40eb795cb9449c5387b62781a711174`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/scilib/df_pivot_spec.spl
mirror: doc/06_spec/03_system/feature/scilib/df_pivot_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/scilib/df_pivot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/scilib/df_pivot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/scilib/df_pivot_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pivots long numeric rows to wide summed columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/df_pivot_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports Float64 index keys' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/scilib/df_pivot_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for missing columns, duplicate roles, and invalid dtypes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
