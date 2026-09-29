# Vhdl Dim Constraints Specification

> Tests covering Vhdl Dim Constraints.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vhdl Dim Constraints Specification

## Scenarios

### Vhdl Dim Constraints

#### accepts and rejects width matches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts and rejects width matches
   - Expected: ok_solver.solve().is_ok() is true
   - Expected: bad_result.is_err() is true
   - Expected: bad_errors.len() equals `1`
   - Expected: bad_errors[0].error_code equals `E0700`
   - Expected: bad_errors[0].kind equals `DimErrorKind.WidthMismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts and rejects width matches")
val ok_solver = DimSolver.new()
ok_solver.add(DimConstraint.WidthMatch(lit(32), lit(32), "<=", test_span()))
expect(ok_solver.solve().is_ok()).to_equal(true)

val bad_solver = DimSolver.new()
bad_solver.add(DimConstraint.WidthMatch(lit(8), lit(16), "<=", test_span()))
val bad_result = bad_solver.solve()

expect(bad_result.is_err()).to_equal(true)
val bad_errors = bad_result.unwrap_err()
expect(bad_errors.len()).to_equal(1)
expect(bad_errors[0].error_code).to_equal("E0700")
expect(bad_errors[0].kind).to_equal(DimErrorKind.WidthMismatch)
```

</details>

#### checks width safety for addition and multiplication

- checks width safety for addition and multiplication
   - Expected: add_ok.solve().is_ok() is true
   - Expected: add_bad_result.is_err() is true
   - Expected: add_bad_result.unwrap_err()[0].error_code equals `E0701`
   - Expected: add_bad_result.unwrap_err()[0].kind equals `DimErrorKind.WidthOverflow`
   - Expected: mul_bad.solve().is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks width safety for addition and multiplication")
val add_ok = DimSolver.new()
add_ok.add(DimConstraint.WidthSafe([lit(16), lit(16)], "+", lit(17), test_span()))
expect(add_ok.solve().is_ok()).to_equal(true)

val add_bad = DimSolver.new()
add_bad.add(DimConstraint.WidthSafe([lit(16), lit(16)], "+", lit(16), test_span()))
val add_bad_result = add_bad.solve()
expect(add_bad_result.is_err()).to_equal(true)
expect(add_bad_result.unwrap_err()[0].error_code).to_equal("E0701")
expect(add_bad_result.unwrap_err()[0].kind).to_equal(DimErrorKind.WidthOverflow)

val mul_bad = DimSolver.new()
mul_bad.add(DimConstraint.WidthSafe([lit(32), lit(32)], "*", lit(32), test_span()))
expect(mul_bad.solve().is_err()).to_equal(true)
```

</details>

<details>
<summary>Advanced: accepts bounded loops within the limit and rejects unbounded ones</summary>

#### accepts bounded loops within the limit and rejects unbounded ones

- accepts bounded loops within the limit and rejects unbounded ones
   - Expected: ok_solver.solve().is_ok() is true
   - Expected: bad_result.is_err() is true
   - Expected: bad_result.unwrap_err()[0].error_code equals `E0730`
   - Expected: bad_result.unwrap_err()[0].kind equals `DimErrorKind.UnboundedLoop`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts bounded loops within the limit and rejects unbounded ones")
val ok_solver = DimSolver.new()
ok_solver.add(DimConstraint.BoundedLoop(lit(256), 1024, test_span()))
expect(ok_solver.solve().is_ok()).to_equal(true)

val bad_solver = DimSolver.new()
bad_solver.add(DimConstraint.BoundedLoop(lit(2048), 1024, test_span()))
val bad_result = bad_solver.solve()

expect(bad_result.is_err()).to_equal(true)
expect(bad_result.unwrap_err()[0].error_code).to_equal("E0730")
expect(bad_result.unwrap_err()[0].kind).to_equal(DimErrorKind.UnboundedLoop)
```

</details>


</details>

#### checks valid ranges in both directions

- checks valid ranges in both directions
   - Expected: ok_solver.solve().is_ok() is true
   - Expected: bad_result.is_err() is true
   - Expected: bad_result.unwrap_err()[0].error_code equals `E0740`
   - Expected: bad_result.unwrap_err()[0].kind equals `DimErrorKind.InvalidRange`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks valid ranges in both directions")
val ok_solver = DimSolver.new()
ok_solver.add(DimConstraint.ValidRange(lit(7), lit(0), test_span()))
expect(ok_solver.solve().is_ok()).to_equal(true)

val bad_solver = DimSolver.new()
bad_solver.add(DimConstraint.ValidRange(lit(3), lit(7), test_span()))
val bad_result = bad_solver.solve()

expect(bad_result.is_err()).to_equal(true)
expect(bad_result.unwrap_err()[0].error_code).to_equal("E0740")
expect(bad_result.unwrap_err()[0].kind).to_equal(DimErrorKind.InvalidRange)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/vhdl_dim_constraints_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vhdl Dim Constraints.
- Vhdl Dim Constraints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a236d079f4151ea169dd4bf985af68c2b015a125c35eea5691fd8f9918ebaf5d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a236d079f4151ea169dd4bf985af68c2b015a125c35eea5691fd8f9918ebaf5d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a236d079f4151ea169dd4bf985af68c2b015a125c35eea5691fd8f9918ebaf5d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/backend/vhdl_dim_constraints_spec.spl
mirror: doc/06_spec/unit/compiler/backend/vhdl_dim_constraints_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/vhdl_dim_constraints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/vhdl_dim_constraints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/vhdl_dim_constraints_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/vhdl_dim_constraints_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts and rejects width matches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_dim_constraints_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checks width safety for addition and multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/vhdl_dim_constraints_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts bounded loops within the limit and rejects unbounded ones' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
