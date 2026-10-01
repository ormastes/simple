# SciPy Stats Facade Specification

> Validates the first SciPy-style namespace slice over typed `NDArray` values.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Stats Facade Specification

Validates the first SciPy-style namespace slice over typed `NDArray` values.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-stats-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_stats_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the first SciPy-style namespace slice over typed `NDArray` values.

## Scenarios

### scipy.stats NDArray facade

#### computes sum, mean, population variance, and population stddev

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes sum, mean, population variance, and population stddev
   - Expected: sum(values).unwrap() equals `Float64.new(6.0)`
   - Expected: mean(values).unwrap() equals `Float64.new(2.0)`
   - Expected: variance(values).unwrap() equals `Float64.new(0.6666666666666666)`
   - Expected: stddev(array([Float64.new(2.0), Float64.new(4.0)])).unwrap() equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes sum, mean, population variance, and population stddev")
val values = array([Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
expect(sum(values).unwrap()).to_equal(Float64.new(6.0))
expect(mean(values).unwrap()).to_equal(Float64.new(2.0))
expect(variance(values).unwrap()).to_equal(Float64.new(0.6666666666666666))
expect(stddev(array([Float64.new(2.0), Float64.new(4.0)])).unwrap()).to_equal(Float64.new(1.0))
```

</details>

#### returns errors for empty mean and variance

- returns errors for empty mean and variance
   - Expected: mean(values).is_err() is true
   - Expected: variance(values).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for empty mean and variance")
val values = array([])
expect(mean(values).is_err()).to_equal(true)
expect(variance(values).is_err()).to_equal(true)
```

</details>

#### returns UnsupportedDType for Int64 inputs

- returns UnsupportedDType for Int64 inputs
   - Expected: sum(values).is_err() is true
   - Expected: variance(values).is_err() is true
   - Expected: zscore(values).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns UnsupportedDType for Int64 inputs")
val values = array_i64([Int64.new(1), Int64.new(2)])
expect(sum(values).is_err()).to_equal(true)
expect(variance(values).is_err()).to_equal(true)
expect(zscore(values).is_err()).to_equal(true)
```

</details>

#### computes population z-scores

- computes population z-scores
   - Expected: result.len() equals `Index.new(2)`
   - Expected: result.flat_f64(0) equals `Float64.new(-1.0)`
   - Expected: result.flat_f64(1) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes population z-scores")
val values = array([Float64.new(2.0), Float64.new(4.0)])
val result = zscore(values).unwrap()
expect(result.len()).to_equal(Index.new(2))
expect(result.flat_f64(0)).to_equal(Float64.new(-1.0))
expect(result.flat_f64(1)).to_equal(Float64.new(1.0))
```

</details>

#### returns errors for invalid z-score inputs

- returns errors for invalid z-score inputs
   - Expected: zscore(array([])).is_err() is true
   - Expected: zscore(array([Float64.new(3.0), Float64.new(3.0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid z-score inputs")
expect(zscore(array([])).is_err()).to_equal(true)
expect(zscore(array([Float64.new(3.0), Float64.new(3.0)])).is_err()).to_equal(true)
```

</details>

#### computes median for odd and even Float64 arrays

- computes median for odd and even Float64 arrays
   - Expected: median(odd).unwrap() equals `Float64.new(2.0)`
   - Expected: median(even).unwrap() equals `Float64.new(2.5)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes median for odd and even Float64 arrays")
val odd = array([Float64.new(3.0), Float64.new(1.0), Float64.new(2.0)])
val even = array([Float64.new(4.0), Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)])
expect(median(odd).unwrap()).to_equal(Float64.new(2.0))
expect(median(even).unwrap()).to_equal(Float64.new(2.5))
```

</details>

#### computes linear quantiles

- computes linear quantiles
   - Expected: quantile(values, Float64.new(0.0)).unwrap() equals `Float64.new(0.0)`
   - Expected: quantile(values, Float64.new(0.25)).unwrap() equals `Float64.new(5.0)`
   - Expected: quantile(values, Float64.new(1.0)).unwrap() equals `Float64.new(20.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes linear quantiles")
val values = array([Float64.new(0.0), Float64.new(10.0), Float64.new(20.0)])
expect(quantile(values, Float64.new(0.0)).unwrap()).to_equal(Float64.new(0.0))
expect(quantile(values, Float64.new(0.25)).unwrap()).to_equal(Float64.new(5.0))
expect(quantile(values, Float64.new(1.0)).unwrap()).to_equal(Float64.new(20.0))
```

</details>

#### returns errors for invalid median and quantile inputs

- returns errors for invalid median and quantile inputs
   - Expected: median(array([])).is_err() is true
   - Expected: quantile(array([Float64.new(1.0)]), Float64.new(-0.1)).is_err() is true
   - Expected: quantile(array_i64([Int64.new(1)]), Float64.new(0.5)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for invalid median and quantile inputs")
expect(median(array([])).is_err()).to_equal(true)
expect(quantile(array([Float64.new(1.0)]), Float64.new(-0.1)).is_err()).to_equal(true)
expect(quantile(array_i64([Int64.new(1)]), Float64.new(0.5)).is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `1cd99405c81512c10d10ac108f04847fea2631b60047e05eb51eb82450961cfd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1cd99405c81512c10d10ac108f04847fea2631b60047e05eb51eb82450961cfd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1cd99405c81512c10d10ac108f04847fea2631b60047e05eb51eb82450961cfd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_stats_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_stats_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_stats_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_stats_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_stats_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes sum, mean, population variance, and population stddev' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_stats_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for empty mean and variance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_stats_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns UnsupportedDType for Int64 inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
