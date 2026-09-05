# SciPy Optimize Facade Specification

> Validates a sampled root-bracketing helper as the first optimize namespace

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SciPy Optimize Facade Specification

Validates a sampled root-bracketing helper as the first optimize namespace

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | science-math-lib-set-scipy-optimize-core |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Source | `test/feature/scilib/scipy_optimize_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a sampled root-bracketing helper as the first optimize namespace
slice over typed `NDArray` values.

## Scenarios

### scipy.optimize bracket_root_linear

#### finds the first sign-change interval

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds the first sign-change interval
   - Expected: bracket.left equals `Float64.new(-1.0)`
   - Expected: bracket.right equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("finds the first sign-change interval")
val x = array([Float64.new(-2.0), Float64.new(-1.0), Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(-3.0), Float64.new(-1.0), Float64.new(1.0), Float64.new(4.0)])
val bracket = bracket_root_linear(x, y).unwrap()
expect(bracket.left).to_equal(Float64.new(-1.0))
expect(bracket.right).to_equal(Float64.new(0.0))
```

</details>

#### returns a point bracket for exact zero samples

- returns a point bracket for exact zero samples
   - Expected: bracket.left equals `Float64.new(0.0)`
   - Expected: bracket.right equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a point bracket for exact zero samples")
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(0.0), Float64.new(2.0)])
val bracket = bracket_root_linear(x, y).unwrap()
expect(bracket.left).to_equal(Float64.new(0.0))
expect(bracket.right).to_equal(Float64.new(0.0))
```

</details>

#### returns errors for missing sign changes and bad dtypes

- returns errors for missing sign changes and bad dtypes
   - Expected: bracket_root_linear(x, y).is_err() is true
   - Expected: bracket_root_linear(array_i64([Int64.new(0), Int64.new(1)]), y).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for missing sign changes and bad dtypes")
val x = array([Float64.new(0.0), Float64.new(1.0)])
val y = array([Float64.new(2.0), Float64.new(3.0)])
expect(bracket_root_linear(x, y).is_err()).to_equal(true)
expect(bracket_root_linear(array_i64([Int64.new(0), Int64.new(1)]), y).is_err()).to_equal(true)
```

</details>

### scipy.optimize minimize_samples

#### returns the sampled minimum value and index

- returns the sampled minimum value and index
   - Expected: result.x equals `Float64.new(0.0)`
   - Expected: result.y equals `Float64.new(2.0)`
   - Expected: result.index equals `Index.new(1)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns the sampled minimum value and index")
val x = array([Float64.new(-1.0), Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(5.0), Float64.new(2.0), Float64.new(3.0), Float64.new(8.0)])
val result = minimize_samples(x, y).unwrap()
expect(result.x).to_equal(Float64.new(0.0))
expect(result.y).to_equal(Float64.new(2.0))
expect(result.index).to_equal(Index.new(1))
```

</details>

#### keeps the first minimum when values tie

- keeps the first minimum when values tie
   - Expected: result.x equals `Float64.new(0.0)`
   - Expected: result.index equals `Index.new(0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("keeps the first minimum when values tie")
val x = array([Float64.new(0.0), Float64.new(1.0), Float64.new(2.0)])
val y = array([Float64.new(1.0), Float64.new(1.0), Float64.new(2.0)])
val result = minimize_samples(x, y).unwrap()
expect(result.x).to_equal(Float64.new(0.0))
expect(result.index).to_equal(Index.new(0))
```

</details>

#### returns errors for empty inputs and mismatched lengths

- returns errors for empty inputs and mismatched lengths
   - Expected: minimize_samples(array([]), array([])).is_err() is true
   - Expected: minimize_samples(x, array([Float64.new(1.0)])).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for empty inputs and mismatched lengths")
val x = array([Float64.new(0.0), Float64.new(1.0)])
expect(minimize_samples(array([]), array([])).is_err()).to_equal(true)
expect(minimize_samples(x, array([Float64.new(1.0)])).is_err()).to_equal(true)
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

- **Plan:** `doc/03_plan/agent_tasks/science_math_lib_set.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `569591abac535ceebb0e85acc37281a36fb74e15cb19070443c1106833ffaa7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `569591abac535ceebb0e85acc37281a36fb74e15cb19070443c1106833ffaa7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `569591abac535ceebb0e85acc37281a36fb74e15cb19070443c1106833ffaa7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/scipy_optimize_spec.spl
mirror: doc/06_spec/feature/scilib/scipy_optimize_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/scipy_optimize_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/scipy_optimize_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/scipy_optimize_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds the first sign-change interval' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_optimize_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a point bracket for exact zero samples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/scipy_optimize_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for missing sign changes and bad dtypes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
