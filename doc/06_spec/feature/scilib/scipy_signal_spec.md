# SciPy Signal Facade Specification

> Validates a first signal-processing namespace slice over typed `NDArray`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Signal Facade Specification

Validates a first signal-processing namespace slice over typed `NDArray`

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-signal-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_signal_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a first signal-processing namespace slice over typed `NDArray`
values.

## Scenarios

### scipy.signal NDArray facade

#### computes full one-dimensional convolution

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes full one-dimensional convolution
   - Expected: result.len() equals `Index.new(4)`
   - Expected: result.flat_f64(0) equals `Float64.new(1.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(3.0)`
   - Expected: result.flat_f64(2) equals `Float64.new(5.0)`
   - Expected: result.flat_f64(3) equals `Float64.new(3.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes full one-dimensional convolution")
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val weights = array([Float64.new(1.0), Float64.new(1.0)])
val result = convolve_full(values, weights).unwrap()
expect(result.len()).to_equal(Index.new(4))
expect(result.flat_f64(0)).to_equal(Float64.new(1.0))
expect(result.flat_f64(1)).to_equal(Float64.new(3.0))
expect(result.flat_f64(2)).to_equal(Float64.new(5.0))
expect(result.flat_f64(3)).to_equal(Float64.new(3.0))
```

</details>

#### computes a valid moving average

- computes a valid moving average
   - Expected: result.len() equals `Index.new(3)`
   - Expected: result.flat_f64(0) equals `Float64.new(3.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(5.0)`
   - Expected: result.flat_f64(2) equals `Float64.new(7.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes a valid moving average")
val values = array([Float64.new(2.0), Float64.new(4.0), Float64.new(6.0), Float64.new(8.0)])
val result = moving_average(values, Index.new(2)).unwrap()
expect(result.len()).to_equal(Index.new(3))
expect(result.flat_f64(0)).to_equal(Float64.new(3.0))
expect(result.flat_f64(1)).to_equal(Float64.new(5.0))
expect(result.flat_f64(2)).to_equal(Float64.new(7.0))
```

</details>

#### computes full one-dimensional correlation

- computes full one-dimensional correlation
   - Expected: result.len() equals `Index.new(4)`
   - Expected: result.flat_f64(0) equals `Float64.new(5.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(14.0)`
   - Expected: result.flat_f64(2) equals `Float64.new(23.0)`
   - Expected: result.flat_f64(3) equals `Float64.new(12.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes full one-dimensional correlation")
val left = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
val right = array([Float64.new(4.0), Float64.new(5.0)])
val result = correlate_full(left, right).unwrap()
expect(result.len()).to_equal(Index.new(4))
expect(result.flat_f64(0)).to_equal(Float64.new(5.0))
expect(result.flat_f64(1)).to_equal(Float64.new(14.0))
expect(result.flat_f64(2)).to_equal(Float64.new(23.0))
expect(result.flat_f64(3)).to_equal(Float64.new(12.0))
```

</details>

#### computes first differences

- computes first differences
   - Expected: result.len() equals `Index.new(2)`
   - Expected: result.flat_f64(0) equals `Float64.new(2.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(-1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes first differences")
val values = array([Float64.new(3.0), Float64.new(5.0), Float64.new(4.0)])
val result = first_difference(values).unwrap()
expect(result.len()).to_equal(Index.new(2))
expect(result.flat_f64(0)).to_equal(Float64.new(2.0))
expect(result.flat_f64(1)).to_equal(Float64.new(-1.0))
```

</details>

#### returns errors for unsupported dtype and invalid window

- returns errors for unsupported dtype and invalid window
   - Expected: convolve_full(array_i64([Int64.new(1)]), values).is_err() is true
   - Expected: correlate_full(values, array_i64([Int64.new(1)])).is_err() is true
   - Expected: moving_average(values, Index.new(0)).is_err() is true
   - Expected: moving_average(values, Index.new(3)).is_err() is true
   - Expected: first_difference(array([Float64.new(1.0)])).is_err() is true
   - Expected: first_difference(array_i64([Int64.new(1), Int64.new(2)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for unsupported dtype and invalid window")
val values = array([Float64.new(1.0), Float64.new(2.0)])
expect(convolve_full(array_i64([Int64.new(1)]), values).is_err()).to_equal(true)
expect(correlate_full(values, array_i64([Int64.new(1)])).is_err()).to_equal(true)
expect(moving_average(values, Index.new(0)).is_err()).to_equal(true)
expect(moving_average(values, Index.new(3)).is_err()).to_equal(true)
expect(first_difference(array([Float64.new(1.0)])).is_err()).to_equal(true)
expect(first_difference(array_i64([Int64.new(1), Int64.new(2)])).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `c24468a41f8c80eafa9276fe415a260177fc1a4cbed0cb644d0ebe80118df0ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c24468a41f8c80eafa9276fe415a260177fc1a4cbed0cb644d0ebe80118df0ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c24468a41f8c80eafa9276fe415a260177fc1a4cbed0cb644d0ebe80118df0ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_signal_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_signal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_signal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_signal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_signal_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes full one-dimensional convolution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_signal_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes a valid moving average' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_signal_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes full one-dimensional correlation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
