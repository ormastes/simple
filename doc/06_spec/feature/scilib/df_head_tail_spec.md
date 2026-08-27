# DataFrame Head And Tail Specification

> Validates row inspection helpers using the same row-gather path as

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DataFrame Head And Tail Specification

Validates row inspection helpers using the same row-gather path as

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | T-DF-18, T-DF-19, science-math-lib-set-pandas-core-head-tail |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/scilib_port_df.md |
| Source | `test/feature/scilib/df_head_tail_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates row inspection helpers using the same row-gather path as
`sort_values`.

## Scenarios

### DataFrame head and tail

#### head returns the first n rows across all columns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- head returns the first n rows across all columns
   - Expected: h.num_rows() equals `Index.new(2)`
   - Expected: h.col(Symbol.from("price")).unwrap().get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: h.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(20)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("head returns the first n rows across all columns")
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
val h = df.head(Index.new(2)).unwrap()
expect(h.num_rows()).to_equal(Index.new(2))
expect(h.col(Symbol.from("price")).unwrap().get(Index.new(1))).to_equal(Float64.new(2.0))
expect(h.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(20))
```

</details>

#### tail returns the last n rows across all columns

- tail returns the last n rows across all columns
   - Expected: t.num_rows() equals `Index.new(2)`
   - Expected: t.col(Symbol.from("price")).unwrap().get(Index.new(0)) equals `Float64.new(2.0)`
   - Expected: t.col(Symbol.from("qty")).unwrap().get(Index.new(1)) equals `Int64.new(30)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("tail returns the last n rows across all columns")
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
val t = df.tail(Index.new(2)).unwrap()
expect(t.num_rows()).to_equal(Index.new(2))
expect(t.col(Symbol.from("price")).unwrap().get(Index.new(0))).to_equal(Float64.new(2.0))
expect(t.col(Symbol.from("qty")).unwrap().get(Index.new(1))).to_equal(Int64.new(30))
```

</details>

#### clamps counts larger than the frame length

- clamps counts larger than the frame length
   - Expected: df.head(Index.new(99)).unwrap().num_rows() equals `Index.new(2)`
   - Expected: df.tail(Index.new(99)).unwrap().num_rows() equals `Index.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("clamps counts larger than the frame length")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0), Float64.new(2.0)]
    )),
]).unwrap()
expect(df.head(Index.new(99)).unwrap().num_rows()).to_equal(Index.new(2))
expect(df.tail(Index.new(99)).unwrap().num_rows()).to_equal(Index.new(2))
```

</details>

#### returns ShapeMismatch for negative counts

- returns ShapeMismatch for negative counts
   - Expected: df.head(Index.new(-1)).is_err() is true
   - Expected: df.tail(Index.new(-1)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns ShapeMismatch for negative counts")
val df = DataFrame.from_columns([
    SeriesErased.F64Series(Series.from_values(
        name: Symbol.from("price"),
        values: [Float64.new(1.0)]
    )),
]).unwrap()
expect(df.head(Index.new(-1)).is_err()).to_equal(true)
expect(df.tail(Index.new(-1)).is_err()).to_equal(true)
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

- **Plan:** `doc/03_plan/agent_tasks/scilib_port_df.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `193a85a44a7cc6d8db4e8ea39007fc3b619d014d6a7e7f579459568a46d1ad11`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `193a85a44a7cc6d8db4e8ea39007fc3b619d014d6a7e7f579459568a46d1ad11`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `193a85a44a7cc6d8db4e8ea39007fc3b619d014d6a7e7f579459568a46d1ad11`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/df_head_tail_spec.spl
mirror: doc/06_spec/feature/scilib/df_head_tail_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/df_head_tail_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/df_head_tail_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/df_head_tail_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'head returns the first n rows across all columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_head_tail_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tail returns the last n rows across all columns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/df_head_tail_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clamps counts larger than the frame length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
