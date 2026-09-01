# LAPACK inv / inverse Specification

> Validates the public inverse operation used by the planned math-block and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LAPACK inv / inverse Specification

Validates the public inverse operation used by the planned math-block and

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-lapack-inv |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/lapack_inv_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the public inverse operation used by the planned math-block and
Fortran-compatible linalg surfaces.

## Scenarios

### linalg.inv

#### returns identity for identity input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns identity for identity input
   - Expected: result.rows() equals `Index.new(3)`
   - Expected: result.cols() equals `Index.new(3)`
   - Expected: result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(1.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(1.0)`
   - Expected: result.get_f64_at([Index.new(2), Index.new(2)]) equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns identity for identity input")
val a = eye_matrix(Index.new(3))
val result = inv(a).unwrap()
expect(result.rows()).to_equal(Index.new(3))
expect(result.cols()).to_equal(Index.new(3))
expect(result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(1.0))
expect(result.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(1.0))
expect(result.get_f64_at([Index.new(2), Index.new(2)])).to_equal(Float64.new(1.0))
```

</details>

<details>
<summary>Advanced: inverts a 2x2 matrix with integer-exact inverse</summary>

#### inverts a 2x2 matrix with integer-exact inverse

- inverts a 2x2 matrix with integer-exact inverse
   - Expected: result.get_f64_at([Index.new(0), Index.new(0)]) equals `Float64.new(0.5)`
   - Expected: result.get_f64_at([Index.new(0), Index.new(1)]) equals `Float64.new(0.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(0)]) equals `Float64.new(0.0)`
   - Expected: result.get_f64_at([Index.new(1), Index.new(1)]) equals `Float64.new(0.25)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("inverts a 2x2 matrix with integer-exact inverse")
val a = matrix_from_rows([
    [Float64.new(2.0), Float64.new(0.0)],
    [Float64.new(0.0), Float64.new(4.0)]])
val result = inv(a).unwrap()
expect(result.get_f64_at([Index.new(0), Index.new(0)])).to_equal(Float64.new(0.5))
expect(result.get_f64_at([Index.new(0), Index.new(1)])).to_equal(Float64.new(0.0))
expect(result.get_f64_at([Index.new(1), Index.new(0)])).to_equal(Float64.new(0.0))
expect(result.get_f64_at([Index.new(1), Index.new(1)])).to_equal(Float64.new(0.25))
```

</details>


</details>

#### returns errors for non-square and singular matrices

- returns errors for non-square and singular matrices
   - Expected: inv(non_square).is_err() is true
   - Expected: inv(singular).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns errors for non-square and singular matrices")
val non_square = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
val singular = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(2.0), Float64.new(4.0)]])
expect(inv(non_square).is_err()).to_equal(true)
expect(inv(singular).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `0338171edf8b2ca0257dd53968249970f69e80c03763c714924483696cc9a597`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0338171edf8b2ca0257dd53968249970f69e80c03763c714924483696cc9a597`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0338171edf8b2ca0257dd53968249970f69e80c03763c714924483696cc9a597`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/lapack_inv_spec.spl
mirror: doc/06_spec/feature/scilib/lapack_inv_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/lapack_inv_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/lapack_inv_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/lapack_inv_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns identity for identity input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/lapack_inv_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'inverts a 2x2 matrix with integer-exact inverse' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/lapack_inv_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns errors for non-square and singular matrices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
