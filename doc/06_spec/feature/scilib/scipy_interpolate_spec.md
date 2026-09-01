# SciPy Interpolate Facade Specification

> Validates a first interpolation namespace slice over typed `NDArray` values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Interpolate Facade Specification

Validates a first interpolation namespace slice over typed `NDArray` values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-interpolate-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_interpolate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first interpolation namespace slice over typed `NDArray` values.

## Scenarios

### scipy.interpolate interp1d_linear

#### linearly interpolates inside a sampled interval

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- linearly interpolates inside a sampled interval
   - Expected: interp1d_linear(x, y, Float64.new(2.5)).unwrap() equals `Float64.new(5.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("linearly interpolates inside a sampled interval")
val x = array([Float64.new(0.0), Float64.new(10.0)])
val y = array([Float64.new(0.0), Float64.new(20.0)])
expect(interp1d_linear(x, y, Float64.new(2.5)).unwrap()).to_equal(Float64.new(5.0))
```

</details>

#### uses the containing interval in a multi-point sample

- uses the containing interval in a multi-point sample
   - Expected: interp1d_linear(x, y, Float64.new(2.0)).unwrap() equals `Float64.new(4.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("uses the containing interval in a multi-point sample")
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(3.0)])
val y = array([Float64.new(0.0), Float64.new(2.0), Float64.new(6.0)])
expect(interp1d_linear(x, y, Float64.new(2.0)).unwrap()).to_equal(Float64.new(4.0))
```

</details>

#### returns errors for out-of-range query and bad dtype

- returns errors for out-of-range query and bad dtype
   - Expected: interp1d_linear(x, y, Float64.new(2.0)).is_err() is true
   - Expected: interp1d_linear(array_i64([Int64.new(0), Int64.new(1)]), y, Float64.new(0.5)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for out-of-range query and bad dtype")
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0), Float64.new(1.0)])
expect(interp1d_linear(x, y, Float64.new(2.0)).is_err()).to_equal(true)
expect(interp1d_linear(array_i64([Int64.new(0), Int64.new(1)]), y, Float64.new(0.5)).is_err()).to_equal(true)
```

</details>

#### linearly interpolates an array of query points

- linearly interpolates an array of query points
   - Expected: result.len() equals `Index.new(3)`
   - Expected: result.flat_f64(0) equals `Float64.new(0.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(5.0)`
   - Expected: result.flat_f64(2) equals `Float64.new(20.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("linearly interpolates an array of query points")
val x = array([Float64.new(0.0), Float64.new(10.0)])
val y = array([Float64.new(0.0), Float64.new(20.0)])
val queries = array([Float64.new(0.0), Float64.new(2.5), Float64.new(10.0)])
val result = interp1d_linear_array(x, y, queries).unwrap()
expect(result.len()).to_equal(Index.new(3))
expect(result.flat_f64(0)).to_equal(Float64.new(0.0))
expect(result.flat_f64(1)).to_equal(Float64.new(5.0))
expect(result.flat_f64(2)).to_equal(Float64.new(20.0))
```

</details>

#### returns errors for invalid query arrays

- returns errors for invalid query arrays
   - Expected: interp1d_linear_array(x, y, array_i64([Int64.new(0)])).is_err() is true
   - Expected: interp1d_linear_array(x, y, array([Float64.new(2.0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid query arrays")
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0), Float64.new(1.0)])
expect(interp1d_linear_array(x, y, array_i64([Int64.new(0)])).is_err()).to_equal(true)
expect(interp1d_linear_array(x, y, array([Float64.new(2.0)])).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `196ff46955dda69bd2d2db52166fa18c4ed59f36489269b619c1823ad9d2e36f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `196ff46955dda69bd2d2db52166fa18c4ed59f36489269b619c1823ad9d2e36f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `196ff46955dda69bd2d2db52166fa18c4ed59f36489269b619c1823ad9d2e36f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_interpolate_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_interpolate_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_interpolate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_interpolate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_interpolate_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'linearly interpolates inside a sampled interval' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_interpolate_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the containing interval in a multi-point sample' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_interpolate_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for out-of-range query and bad dtype' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
