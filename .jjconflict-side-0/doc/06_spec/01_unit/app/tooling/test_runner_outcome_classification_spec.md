# Test Runner Outcome Classification Specification

> Tests covering test runner outcome classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Outcome Classification Specification

## Scenarios

### test runner outcome classification

#### classifies pass assertion internal empty and timeout results

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies pass assertion internal empty and timeout results
   - Expected: test_run_outcome_name(classify_test_run_result(pass_result, false)) equals `pass`
   - Expected: test_run_outcome_name(classify_test_run_result(assertion_result, false)) equals `assertion_or_child_failure`
   - Expected: test_run_outcome_name(classify_test_run_result(internal_result, false)) equals `internal_error`
   - Expected: test_run_outcome_name(classify_test_run_result(empty_result, false)) equals `empty_selection`
   - Expected: test_run_outcome_name(classify_test_run_result(timeout_result, false)) equals `timeout_resource_failure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("classifies pass assertion internal empty and timeout results")
val pass_result = outcome_run([outcome_file(0, "", false)], 0, 0)
val assertion_result = outcome_run([outcome_file(1, "assertion failed", false)], 1, 0)
val internal_result = outcome_run([outcome_file(0, "child protocol error", false)], 0, 0)
val empty_result = outcome_run([], 0, 0)
val timeout_result = outcome_run([outcome_file(1, "timeout", true)], 1, 1)

expect(test_run_outcome_name(classify_test_run_result(pass_result, false))).to_equal("pass")
expect(test_run_outcome_name(classify_test_run_result(assertion_result, false))).to_equal("assertion_or_child_failure")
expect(test_run_outcome_name(classify_test_run_result(internal_result, false))).to_equal("internal_error")
expect(test_run_outcome_name(classify_test_run_result(empty_result, false))).to_equal("empty_selection")
expect(test_run_outcome_name(classify_test_run_result(timeout_result, false))).to_equal("timeout_resource_failure")
```

</details>

#### keeps list-style empty results successful

- keeps list-style empty results successful
   - Expected: test_run_outcome_name(classify_test_run_result(empty_result, true)) equals `pass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps list-style empty results successful")
val empty_result = outcome_run([], 0, 0)

expect(test_run_outcome_name(classify_test_run_result(empty_result, true))).to_equal("pass")
```

</details>

#### publishes stable exit codes for every top-level class

- publishes stable exit codes for every top-level class
   - Expected: test_run_outcome_exit_code(TestRunOutcome.Pass) equals `0`
   - Expected: test_run_outcome_exit_code(TestRunOutcome.AssertionOrChildFailure) equals `1`
   - Expected: test_run_outcome_exit_code(TestRunOutcome.UsageError) equals `2`
   - Expected: test_run_outcome_exit_code(TestRunOutcome.InternalError) equals `3`
   - Expected: test_run_outcome_exit_code(TestRunOutcome.EmptySelection) equals `4`
   - Expected: test_run_outcome_exit_code(TestRunOutcome.TimeoutResourceFailure) equals `124`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("publishes stable exit codes for every top-level class")
expect(test_run_outcome_exit_code(TestRunOutcome.Pass)).to_equal(0)
expect(test_run_outcome_exit_code(TestRunOutcome.AssertionOrChildFailure)).to_equal(1)
expect(test_run_outcome_exit_code(TestRunOutcome.UsageError)).to_equal(2)
expect(test_run_outcome_exit_code(TestRunOutcome.InternalError)).to_equal(3)
expect(test_run_outcome_exit_code(TestRunOutcome.EmptySelection)).to_equal(4)
expect(test_run_outcome_exit_code(TestRunOutcome.TimeoutResourceFailure)).to_equal(124)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/test_runner_outcome_classification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test runner outcome classification.
- test runner outcome classification

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bc963827cbc6135ec554afcbf843998778c13c953e95ee17393fdabc708235c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bc963827cbc6135ec554afcbf843998778c13c953e95ee17393fdabc708235c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bc963827cbc6135ec554afcbf843998778c13c953e95ee17393fdabc708235c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/tooling/test_runner_outcome_classification_spec.spl
mirror: doc/06_spec/01_unit/app/tooling/test_runner_outcome_classification_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/tooling/test_runner_outcome_classification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/tooling/test_runner_outcome_classification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/tooling/test_runner_outcome_classification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/tooling/test_runner_outcome_classification_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies pass assertion internal empty and timeout results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/test_runner_outcome_classification_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps list-style empty results successful' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/tooling/test_runner_outcome_classification_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes stable exit codes for every top-level class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
