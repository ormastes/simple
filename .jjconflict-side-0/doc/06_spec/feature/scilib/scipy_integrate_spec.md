# SciPy Integrate Facade Specification

> Validates the first SciPy-style integration namespace slice over typed

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Integrate Facade Specification

Validates the first SciPy-style integration namespace slice over typed

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-integrate-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_integrate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first SciPy-style integration namespace slice over typed
`NDArray` values.

## Scenarios

### scipy.integrate trapezoid

#### integrates y=x over [0, 2] using sampled points

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- integrates y=x over [0, 2] using sampled points
   - Expected: trapezoid(y, x).unwrap() equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("integrates y=x over [0, 2] using sampled points")
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
expect(trapezoid(y, x).unwrap()).to_equal(Float64.new(2.0))
```

</details>

#### integrates constant values with non-unit spacing

- integrates constant values with non-unit spacing
   - Expected: trapezoid(y, x).unwrap() equals `Float64.new(15.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("integrates constant values with non-unit spacing")
val x = array([Float64.new(0.0), Float64.new(2.0), Float64.new(5.0)])
val y = array([Float64.new(3.0), Float64.new(3.0), Float64.new(3.0)])
expect(trapezoid(y, x).unwrap()).to_equal(Float64.new(15.0))
```

</details>

#### returns errors for mismatched lengths and unsupported dtypes

- returns errors for mismatched lengths and unsupported dtypes
   - Expected: trapezoid(y, x).is_err() is true
   - Expected: trapezoid(array_i64([Int64.new(1), Int64.new(2)]), x).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for mismatched lengths and unsupported dtypes")
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0)])
expect(trapezoid(y, x).is_err()).to_equal(true)
expect(trapezoid(array_i64([Int64.new(1), Int64.new(2)]), x).is_err()).to_equal(true)
```

</details>

### scipy.integrate cumulative_trapezoid

#### returns cumulative area with an initial zero

- returns cumulative area with an initial zero
   - Expected: result.len() equals `Index.new(3)`
   - Expected: result.flat_f64(0) equals `Float64.new(0.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(0.5)`
   - Expected: result.flat_f64(2) equals `Float64.new(2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns cumulative area with an initial zero")
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val result = cumulative_trapezoid(y, x).unwrap()
expect(result.len()).to_equal(Index.new(3))
expect(result.flat_f64(0)).to_equal(Float64.new(0.0))
expect(result.flat_f64(1)).to_equal(Float64.new(0.5))
expect(result.flat_f64(2)).to_equal(Float64.new(2.0))
```

</details>

#### returns errors for mismatched lengths and unsupported dtypes

- returns errors for mismatched lengths and unsupported dtypes
   - Expected: cumulative_trapezoid(array([Float64.new(0.0)]), x).is_err() is true
   - Expected: cumulative_trapezoid(array_i64([Int64.new(1), Int64.new(2)]), x).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for mismatched lengths and unsupported dtypes")
val x = array([Float64.new(0.0), Float64.new(1.0)])
expect(cumulative_trapezoid(array([Float64.new(0.0)]), x).is_err()).to_equal(true)
expect(cumulative_trapezoid(array_i64([Int64.new(1), Int64.new(2)]), x).is_err()).to_equal(true)
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
- **Design:** `doc/05_design/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `85643387faaafdb8bc2d4d029d7d3dcfa90f7df2ec4bd4f746c6988031408708`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `85643387faaafdb8bc2d4d029d7d3dcfa90f7df2ec4bd4f746c6988031408708`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `85643387faaafdb8bc2d4d029d7d3dcfa90f7df2ec4bd4f746c6988031408708`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_integrate_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_integrate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_integrate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_integrate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_integrate_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integrates y=x over [0, 2] using sampled points' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_integrate_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integrates constant values with non-unit spacing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_integrate_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for mismatched lengths and unsupported dtypes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
