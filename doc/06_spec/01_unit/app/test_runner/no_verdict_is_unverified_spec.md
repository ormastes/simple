# no_verdict_is_unverified_spec

> Regression spec for the silent-green defect: a spec whose child produced no

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# no_verdict_is_unverified_spec

Regression spec for the silent-green defect: a spec whose child produced no

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner/no_verdict_is_unverified_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Regression spec for the silent-green defect: a spec whose child produced no
result line must be classified `unverified` and must NOT exit 0.

Requirement R3, doc/02_requirements/infra/supervised_test_runner.md:
"Exit 0 must mean 'every spec produced a verdict and all verdicts passed' --
nothing weaker."

Bug: doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md

The no-verdict shape is reachable in the daemon lane: on TRESP_COMPLETED the
runner builds a TestFileResult with error:"" (test_runner_main.spl:844-861), so
a completed-but-empty child yields passed=failed=skipped=pending=0 with no
error. Before this fix classify_test_run_result fell through that case to
TestRunOutcome.Pass -> exit 0.

Host interference (SIGTERM/SIGKILL/earlyoom) and timeouts are UNVERIFIED, never
failure verdicts about the code -- conflating them is how a contended host
manufactures phantom compiler bugs.

## Scenarios

### test run verdict classification

#### classifies a child that produced no result line as unverified, not pass

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies a child that produced no result line as unverified, not pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies a child that produced no result line as unverified, not pass")
val result = run_of([file_result("no_verdict_spec.spl", 0, 0, "")], 0, 0)
val outcome = classify_test_run_result(result, false)
assert_equal(test_run_outcome_name(outcome), "unverified")
```

</details>

#### gives a no-verdict run a non-zero exit code

- gives a no-verdict run a non-zero exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gives a no-verdict run a non-zero exit code")
val result = run_of([file_result("no_verdict_spec.spl", 0, 0, "")], 0, 0)
val code = test_run_outcome_exit_code(classify_test_run_result(result, false))
assert_not_equal(code, 0)
assert_equal(code, 5)
```

</details>

#### still reports a genuinely passing run as pass with exit 0

- still reports a genuinely passing run as pass with exit 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reports a genuinely passing run as pass with exit 0")
val result = run_of([file_result("good_spec.spl", 3, 0, "")], 3, 0)
val outcome = classify_test_run_result(result, false)
assert_equal(test_run_outcome_name(outcome), "pass")
assert_equal(test_run_outcome_exit_code(outcome), 0)
```

</details>

#### still reports a real assertion failure as a failure

- still reports a real assertion failure as a failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reports a real assertion failure as a failure")
val result = run_of([file_result("bad_spec.spl", 1, 2, "")], 1, 2)
val outcome = classify_test_run_result(result, false)
assert_equal(test_run_outcome_name(outcome), "assertion_or_child_failure")
assert_equal(test_run_outcome_exit_code(outcome), 1)
```

</details>

#### treats a host SIGTERM kill as unverified, never as a failure verdict

- treats a host SIGTERM kill as unverified, never as a failure verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a host SIGTERM kill as unverified, never as a failure verdict")
val killed = file_result("killed_spec.spl", 0, 0, "TERMINATED: killed by signal 15")
val outcome = classify_test_run_result(run_of([killed], 0, 0), false)
assert_equal(test_run_outcome_name(outcome), "unverified")
assert_not_equal(test_run_outcome_name(outcome), "assertion_or_child_failure")
```

</details>

#### treats a timeout as unverified, never as a failure verdict

- treats a timeout as unverified, never as a failure verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a timeout as unverified, never as a failure verdict")
val timed = file_result("slow_spec.spl", 0, 0, "TIMEOUT: exceeded budget")
val outcome = classify_test_run_result(run_of([timed], 0, 0), false)
assert_equal(test_run_outcome_name(outcome), "unverified")
```

</details>

#### treats a never-executed spec as unverified, never as a pass

- treats a never-executed spec as unverified, never as a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a never-executed spec as unverified, never as a pass")
val skipped = file_result("never_ran_spec.spl", 0, 0, "NOT EXECUTED: discovered but never run")
val outcome = classify_test_run_result(run_of([skipped], 0, 0), false)
assert_equal(test_run_outcome_name(outcome), "unverified")
assert_not_equal(test_run_outcome_exit_code(outcome), 0)
```

</details>

#### still reports a crash as an internal error, distinct from unverified

- still reports a crash as an internal error, distinct from unverified


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still reports a crash as an internal error, distinct from unverified")
val crashed = file_result("crash_spec.spl", 0, 0, "CRASHED: signal 11")
val outcome = classify_test_run_result(run_of([crashed], 0, 0), false)
assert_equal(test_run_outcome_name(outcome), "internal_error")
```

</details>

#### identifies the unverified file results individually so they can be named

- identifies the unverified file results individually so they can be named


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identifies the unverified file results individually so they can be named")
assert_true(test_file_result_is_unverified(file_result("a.spl", 0, 0, "")))
assert_true(test_file_result_is_unverified(file_result("b.spl", 0, 0, "TERMINATED: sig 15")))
assert_false(test_file_result_is_unverified(file_result("c.spl", 4, 0, "")))
assert_false(test_file_result_is_unverified(file_result("d.spl", 0, 1, "")))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `5fe4892fd12a091172340aa05de0aee715ab6d7904ef7fd7ca8ee6957c9accba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fe4892fd12a091172340aa05de0aee715ab6d7904ef7fd7ca8ee6957c9accba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fe4892fd12a091172340aa05de0aee715ab6d7904ef7fd7ca8ee6957c9accba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/test_runner/no_verdict_is_unverified_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner/no_verdict_is_unverified_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner/no_verdict_is_unverified_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner/no_verdict_is_unverified_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner/no_verdict_is_unverified_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies a child that produced no result line as unverified, not pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner/no_verdict_is_unverified_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives a no-verdict run a non-zero exit code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner/no_verdict_is_unverified_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still reports a genuinely passing run as pass with exit 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
