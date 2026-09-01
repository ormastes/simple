# LAPACK det / determinant Specification

> Validates a scalar determinant helper over the public linalg facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LAPACK det / determinant Specification

Validates a scalar determinant helper over the public linalg facade.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | scilib-lapack-det |
| Category | Other |
| Status | Active |
| Plan | doc/03_plan/agent_tasks/science_math_lib_set.md |
| Design | doc/05_design/science_math_lib_set.md |
| Source | `test/feature/scilib/lapack_det_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates a scalar determinant helper over the public linalg facade.

## Scenarios

### linalg.det

#### returns one for identity matrices

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns one for identity matrices
   - Expected: det(eye_matrix(Index.new(3))).unwrap() equals `Float64.new(1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns one for identity matrices")
expect(det(eye_matrix(Index.new(3))).unwrap()).to_equal(Float64.new(1.0))
```

</details>

<details>
<summary>Advanced: computes determinant for a 2x2 matrix</summary>

#### computes determinant for a 2x2 matrix

- computes determinant for a 2x2 matrix
   - Expected: det(a).unwrap() equals `Float64.new(-2.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("computes determinant for a 2x2 matrix")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(3.0), Float64.new(4.0)]])
expect(det(a).unwrap()).to_equal(Float64.new(-2.0))
```

</details>


</details>

#### accounts for row swaps during pivoting

- accounts for row swaps during pivoting
   - Expected: det(a).unwrap() equals `Float64.new(-1.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("accounts for row swaps during pivoting")
val a = matrix_from_rows([
    [Float64.new(0.0), Float64.new(1.0)],
    [Float64.new(1.0), Float64.new(0.0)]])
expect(det(a).unwrap()).to_equal(Float64.new(-1.0))
```

</details>

#### returns zero for singular matrices

- returns zero for singular matrices
   - Expected: det(a).unwrap() equals `Float64.new(0.0)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns zero for singular matrices")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0)],
    [Float64.new(2.0), Float64.new(4.0)]])
expect(det(a).unwrap()).to_equal(Float64.new(0.0))
```

</details>

#### returns an error for non-square matrices

- returns an error for non-square matrices
   - Expected: det(a).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns an error for non-square matrices")
val a = matrix_from_rows([
    [Float64.new(1.0), Float64.new(2.0), Float64.new(3.0)],
    [Float64.new(4.0), Float64.new(5.0), Float64.new(6.0)]])
expect(det(a).is_err()).to_equal(true)
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

- Canonical SPipe generation for source `5eab766e132b1d50b02d430ef2dd20b21651de8bb772204240ff18d2638494e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5eab766e132b1d50b02d430ef2dd20b21651de8bb772204240ff18d2638494e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5eab766e132b1d50b02d430ef2dd20b21651de8bb772204240ff18d2638494e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/scilib/lapack_det_spec.spl
mirror: doc/06_spec/feature/scilib/lapack_det_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/scilib/lapack_det_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/scilib/lapack_det_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/scilib/lapack_det_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns one for identity matrices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/lapack_det_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes determinant for a 2x2 matrix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/scilib/lapack_det_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accounts for row swaps during pivoting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
