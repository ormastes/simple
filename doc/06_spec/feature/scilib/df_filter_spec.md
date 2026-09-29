# DataFrame Boolean Filter Specification

> Validates `DataFrame.filter(mask: NDArray<Bool>)`, preserving heterogeneous

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Boolean Filter Specification

Validates `DataFrame.filter(mask: NDArray<Bool>)`, preserving heterogeneous

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-10, science-math-lib-set-pandas-core-filter |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/df_filter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates `DataFrame.filter(mask: NDArray<Bool>)`, preserving heterogeneous
column dtypes while filtering rows.

## Scenarios

### DataFrame filter with boolean mask

#### filters rows and preserves Float64 and Int64 column dtypes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- filters rows and preserves Float64 and Int64 column dtypes
   - Expected: filtered.num_rows() equals `Index.new(2)`
   - Expected: filtered.num_cols() equals `Index.new(2)`
   - Expected: filtered.col(Symbol.from("price")).unwrap().get(Index.new(1)) equals `Float64.new(3.0)`
   - Expected: filtered.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(30)`
   - Expected: filtered.dtypes().dtype_at(Index.new(1)) equals `DType.I64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("filters rows and preserves Float64 and Int64 column dtypes")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)]
    )),
    SeriesErased.I64Series(Series.from_values(
        name: Symbol.from("qty"),
        values: [Int64.new(10), Int64.new(20), Int64.new(30)]
    )),
]).unwrap()
val filtered = df.filter(array_bool([Bool.new(true), Bool.new(false), Bool.new(true)])).unwrap()
expect(filtered.num_rows()).to_equal(Index.new(2))
expect(filtered.num_cols()).to_equal(Index.new(2))
expect(filtered.col(Symbol.from("price")).unwrap().get(Index.new(1))).to_equal(Float64.new(3.0))
expect(filtered.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(30))
expect(filtered.dtypes().dtype_at(Index.new(1))).to_equal(DType.I64)
```

</details>

#### returns ShapeMismatch when mask length differs from row count

- returns ShapeMismatch when mask length differs from row count
   - Expected: df.filter(array_bool([Bool.new(true)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns ShapeMismatch when mask length differs from row count")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
expect(df.filter(array_bool([Bool.new(true)])).is_err()).to_equal(true)
```

</details>

#### returns ShapeMismatch when mask dtype is not Bool

- returns ShapeMismatch when mask dtype is not Bool
   - Expected: df.filter(array_i64([Int64.new(1), Int64.new(0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns ShapeMismatch when mask dtype is not Bool")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
expect(df.filter(array_i64([Int64.new(1), Int64.new(0)])).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `7df10945eb3643daa31090fd61fa73a88b50beb49be090c6d47ac49a6abfe520`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7df10945eb3643daa31090fd61fa73a88b50beb49be090c6d47ac49a6abfe520`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7df10945eb3643daa31090fd61fa73a88b50beb49be090c6d47ac49a6abfe520`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_filter_spec.spl
mirror: doc/06_spec/feature/scilib/df_filter_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_filter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_filter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_filter_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters rows and preserves Float64 and Int64 column dtypes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_filter_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ShapeMismatch when mask length differs from row count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_filter_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ShapeMismatch when mask dtype is not Bool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
