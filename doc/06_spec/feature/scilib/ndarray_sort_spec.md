# NDArray Sort And Argsort Specification

> Validates stable 1-D sort and argsort infrastructure used by later DataFrame

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NDArray Sort And Argsort Specification

Validates stable 1-D sort and argsort infrastructure used by later DataFrame

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-numpy-core-sort |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/feature/scilib/ndarray_sort_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**DF dependency:** doc/03_plan/agent_tasks/scilib_port_df.md T-DF-19/T-DF-21

Validates stable 1-D sort and argsort infrastructure used by later DataFrame
sort/groupby work.

## Scenarios

### NDArray argsort

#### returns stable ascending indices for Float64 values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns stable ascending indices for Float64 values
   - Expected: idx.dtype equals `DType.I64`
   - Expected: idx.get(Index.new(0)) equals `Int64.new(1)`
   - Expected: idx.get(Index.new(1)) equals `Int64.new(3)`
   - Expected: idx.get(Index.new(2)) equals `Int64.new(0)`
   - Expected: idx.get(Index.new(3)) equals `Int64.new(2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns stable ascending indices for Float64 values")
val a = array([Float64.new(3.0), Float64.new(1.0), Float64.new(3.0), Float64.new(2.0)])
val idx = a.argsort()
expect(idx.dtype).to_equal(DType.I64)
expect(idx.get(Index.new(0))).to_equal(Int64.new(1))
expect(idx.get(Index.new(1))).to_equal(Int64.new(3))
expect(idx.get(Index.new(2))).to_equal(Int64.new(0))
expect(idx.get(Index.new(3))).to_equal(Int64.new(2))
```

</details>

#### returns ascending indices for Int64 values

- returns ascending indices for Int64 values
   - Expected: idx.get(Index.new(0)) equals `Int64.new(1)`
   - Expected: idx.get(Index.new(1)) equals `Int64.new(2)`
   - Expected: idx.get(Index.new(2)) equals `Int64.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns ascending indices for Int64 values")
val a = array_i64([Int64.new(9), Int64.new(-2), Int64.new(4)])
val idx = a.argsort()
expect(idx.get(Index.new(0))).to_equal(Int64.new(1))
expect(idx.get(Index.new(1))).to_equal(Int64.new(2))
expect(idx.get(Index.new(2))).to_equal(Int64.new(0))
```

</details>

### NDArray sort

#### sorts Float64 values using argsort and gather

- sorts Float64 values using argsort and gather
   - Expected: sorted.get(Index.new(0)) equals `Float64.new(1.0)`
   - Expected: sorted.get(Index.new(1)) equals `Float64.new(2.0)`
   - Expected: sorted.get(Index.new(2)) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sorts Float64 values using argsort and gather")
val sorted = array([Float64.new(3.0), Float64.new(1.0), Float64.new(2.0)]).sort()
expect(sorted.get(Index.new(0))).to_equal(Float64.new(1.0))
expect(sorted.get(Index.new(1))).to_equal(Float64.new(2.0))
expect(sorted.get(Index.new(2))).to_equal(Float64.new(3.0))
```

</details>

#### sorts Int64 values without changing dtype

- sorts Int64 values without changing dtype
   - Expected: sorted.dtype equals `DType.I64`
   - Expected: sorted.get(Index.new(0)) equals `Int64.new(1)`
   - Expected: sorted.get(Index.new(2)) equals `Int64.new(3)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("sorts Int64 values without changing dtype")
val sorted = array_i64([Int64.new(3), Int64.new(1), Int64.new(2)]).sort()
expect(sorted.dtype).to_equal(DType.I64)
expect(sorted.get(Index.new(0))).to_equal(Int64.new(1))
expect(sorted.get(Index.new(2))).to_equal(Int64.new(3))
```

</details>

#### returns UnsupportedDType for Bool argsort

- returns UnsupportedDType for Bool argsort
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns UnsupportedDType for Bool argsort")
val result = array_bool([Bool.new(true), Bool.new(false)]).try_argsort()
expect(result.is_err()).to_equal(true)
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


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `33e544c9d2054cc7d7db5bd91d16254a94d8ccb055ba52480fe27c4a81d7a8cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `33e544c9d2054cc7d7db5bd91d16254a94d8ccb055ba52480fe27c4a81d7a8cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `33e544c9d2054cc7d7db5bd91d16254a94d8ccb055ba52480fe27c4a81d7a8cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/ndarray_sort_spec.spl
mirror: doc/06_spec/feature/scilib/ndarray_sort_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/ndarray_sort_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/ndarray_sort_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/ndarray_sort_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns stable ascending indices for Float64 values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_sort_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns ascending indices for Int64 values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/ndarray_sort_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sorts Float64 values using argsort and gather' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
