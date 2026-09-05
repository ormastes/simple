# DataFrame Merge Specification

> Validates numeric-key merge/join behavior, including missing-value masks for

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Merge Specification

Validates numeric-key merge/join behavior, including missing-value masks for

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-24, T-DF-25, T-DF-26, science-math-lib-set-pandas-core-inner-merge |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Source | `test/feature/scilib/df_merge_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates numeric-key merge/join behavior, including missing-value masks for
unmatched rows in left/right/outer joins.

## Scenarios

### DataFrame merge

#### keeps only matching rows and appends right non-key columns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps only matching rows and appends right non-key columns
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.num_cols() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(0)) equals `Int64.new(2)`
   - Expected: out.col(Symbol.from("price")).unwrap().get(Index.new(1)) equals `Float64.new(30.0)`
   - Expected: out.col(Symbol.from("discount")).unwrap().get(Index.new(1)) equals `Float64.new(0.3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps only matching rows and appends right non-key columns")
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2), Int64.new(3)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0), Float64.new(20.0), Float64.new(30.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2), Int64.new(3), Int64.new(4)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.2), Float64.new(0.3), Float64.new(0.4)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Inner).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.num_cols()).to_equal(Index.new(3))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(0))).to_equal(Int64.new(2))
expect(out.col(Symbol.from("price")).unwrap().get(Index.new(1))).to_equal(Float64.new(30.0))
expect(out.col(Symbol.from("discount")).unwrap().get(Index.new(1))).to_equal(Float64.new(0.3))
```

</details>

#### supports the DataFrame.join method wrapper

- supports the DataFrame.join method wrapper
   - Expected: out.num_rows() equals `Index.new(1)`
   - Expected: out.col(Symbol.from("score")).unwrap().get(Index.new(0)) equals `Float64.new(9.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("supports the DataFrame.join method wrapper")
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("score"), [Float64.new(9.0)])),
]).unwrap()
val out = left.join(right, Symbol.from("id"), JoinHow.Inner).unwrap()
expect(out.num_rows()).to_equal(Index.new(1))
expect(out.col(Symbol.from("score")).unwrap().get(Index.new(0))).to_equal(Float64.new(9.0))
```

</details>

#### left join preserves left rows and marks missing right values

- left join preserves left rows and marks missing right values
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(0)) equals `Int64.new(1)`
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap() is true
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("left join preserves left rows and marks missing right values")
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0), Float64.new(20.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.2)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Left).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(0))).to_equal(Int64.new(1))
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap()).to_equal(true)
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(false)
```

</details>

#### right join preserves right rows and fills missing left columns

- right join preserves right rows and fills missing left columns
   - Expected: out.num_rows() equals `Index.new(2)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(1)) equals `Int64.new(2)`
   - Expected: out.col(Symbol.from("price")).unwrap().is_missing(Index.new(1)).unwrap() is true
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("right join preserves right rows and fills missing left columns")
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.1), Float64.new(0.2)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Right).unwrap()
expect(out.num_rows()).to_equal(Index.new(2))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(1))).to_equal(Int64.new(2))
expect(out.col(Symbol.from("price")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(true)
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(1)).unwrap()).to_equal(false)
```

</details>

#### outer join includes unmatched rows from both sides

- outer join includes unmatched rows from both sides
   - Expected: out.num_rows() equals `Index.new(3)`
   - Expected: out.col(Symbol.from("id")).unwrap().get(Index.new(2)) equals `Int64.new(3)`
   - Expected: out.col(Symbol.from("price")).unwrap().is_missing(Index.new(2)).unwrap() is true
   - Expected: out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("outer join includes unmatched rows from both sides")
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1), Int64.new(2)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("price"), [Float64.new(10.0), Float64.new(20.0)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(2), Int64.new(3)])),
    SeriesErased.F64Series(Series.from_values(Symbol.from("discount"), [Float64.new(0.2), Float64.new(0.3)])),
]).unwrap()
val out = merge(left, right, Symbol.from("id"), JoinHow.Outer).unwrap()
expect(out.num_rows()).to_equal(Index.new(3))
expect(out.col(Symbol.from("id")).unwrap().get(Index.new(2))).to_equal(Int64.new(3))
expect(out.col(Symbol.from("price")).unwrap().is_missing(Index.new(2)).unwrap()).to_equal(true)
expect(out.col(Symbol.from("discount")).unwrap().is_missing(Index.new(0)).unwrap()).to_equal(true)
```

</details>

#### returns errors for missing keys

- returns errors for missing keys
   - Expected: merge(left, right, Symbol.from("id"), JoinHow.Inner).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for missing keys")
val left = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("id"), [Int64.new(1)])),
]).unwrap()
val right = DataFrame.from_columns([
    SeriesErased.I64Series(Series.from_values(Symbol.from("other_id"), [Int64.new(1)])),
]).unwrap()
expect(merge(left, right, Symbol.from("id"), JoinHow.Inner).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `b4c9eb7ebf0c4992efd76f3f33ae717b432aecba7d7f58f17c5274df5dd6bf86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b4c9eb7ebf0c4992efd76f3f33ae717b432aecba7d7f58f17c5274df5dd6bf86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b4c9eb7ebf0c4992efd76f3f33ae717b432aecba7d7f58f17c5274df5dd6bf86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_merge_spec.spl
mirror: doc/06_spec/feature/scilib/df_merge_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_merge_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_merge_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_merge_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps only matching rows and appends right non-key columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_merge_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports the DataFrame.join method wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_merge_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'left join preserves left rows and marks missing right values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
