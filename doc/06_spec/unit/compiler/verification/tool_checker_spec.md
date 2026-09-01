# Tool Checker Specification

> Tests covering Lean Verification Tool Checker.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tool Checker Specification

## Scenarios

### Lean Verification Tool Checker

#### inventory

#### uses the authoritative Lean artifact list

- uses the authoritative Lean artifact list
   - Expected: files.len() equals `15`
   - Expected: files contains `src/verification/nogc_compile/src/NogcCompile.lean`
   - Expected: files contains `src/verification/type_inference_compile/src/Contracts.lean`
   - Expected: files contains `src/verification/tensor_dimensions/src/TensorMemory.lean`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the authoritative Lean artifact list")
val files = checker.known_verification_files()

expect(files.len()).to_equal(15)
expect(files.contains("src/verification/nogc_compile/src/NogcCompile.lean")).to_equal(true)
expect(files.contains("src/verification/type_inference_compile/src/Contracts.lean")).to_equal(true)
expect(files.contains("src/verification/tensor_dimensions/src/TensorMemory.lean")).to_equal(true)
```

</details>

#### summary formatting

#### renders failed proof results with sorry details

- renders failed proof results with sorry details


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders failed proof results with sorry details")
val result = checker.ProofResult(
    file_path: "src/verification/demo/src/Demo.lean",
    status: checker.ProofStatus.Failed,
    sorry_count: 2,
    error_message: "contains sorry",
    theorem_count: 3
)

expect(result.summary_line()).to_contain("[failed]")
expect(result.summary_line()).to_contain("3 theorems")
expect(result.summary_line()).to_contain("2 sorry")
expect(result.summary_line()).to_contain("contains sorry")
```

</details>

#### aggregates verification summary counts

- aggregates verification summary counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("aggregates verification summary counts")
val ok = checker.ProofResult(
    file_path: "src/verification/a.lean",
    status: checker.ProofStatus.ModelProven,
    sorry_count: 0,
    error_message: "",
    theorem_count: 2
)
val bad = checker.ProofResult(
    file_path: "src/verification/b.lean",
    status: checker.ProofStatus.Failed,
    sorry_count: 1,
    error_message: "contains sorry",
    theorem_count: 1
)

val summary = checker.CheckResult(file_results: [ok, bad]).summary()
expect(summary).to_contain("Files checked: 2")
expect(summary).to_contain("Model proven: 1")
expect(summary).to_contain("Failed:    1")
expect(summary).to_contain("Theorems: 3")
expect(summary).to_contain("Pending proofs (sorry): 1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/verification/tool_checker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean Verification Tool Checker.
- Lean Verification Tool Checker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `8e2df74381dd50198dada8c3b3eeedb6a1097422ea218acfcea6650e559dacc5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e2df74381dd50198dada8c3b3eeedb6a1097422ea218acfcea6650e559dacc5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e2df74381dd50198dada8c3b3eeedb6a1097422ea218acfcea6650e559dacc5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/verification/tool_checker_spec.spl
mirror: doc/06_spec/unit/compiler/verification/tool_checker_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/verification/tool_checker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/verification/tool_checker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/verification/tool_checker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/verification/tool_checker_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the authoritative Lean artifact list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/tool_checker_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders failed proof results with sorry details' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/tool_checker_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'aggregates verification summary counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
