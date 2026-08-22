# test_runner_output_outcome_class_spec

> Verifies the test runner output outcome class behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_runner_output_outcome_class_spec

Verifies the test runner output outcome class behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the test runner output outcome class behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### test_runner_output outcome classification

#### classifies on the class token, not on the message wording

- Verify: classifies on the class token, not on the message wording


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R6
step("Verify: classifies on the class token, not on the message wording")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""A lane may reword the message after the colon at any time; the class
must be unchanged."""
assert_equal(test_file_outcome_class(mk("CRASHED: child died by signal", 1, 0, false)), "CRASHED")
assert_equal(test_file_outcome_class(mk("CRASHED: some completely different wording", 1, 0, false)), "CRASHED")
assert_equal(test_file_outcome_class(mk("TERMINATED: killed by SIGTERM", 0, 0, false)), "TERMINATED")
assert_equal(test_file_outcome_class(mk("TIMEOUT: exceeded 600s", 0, 0, false)), "TIMEOUT")
assert_equal(test_file_outcome_class(mk("NOT EXECUTED: discovered but never run", 0, 0, false)), "NOT_RUN")
```

</details>

#### accepts the NOT_RUN spelling as well as NOT EXECUTED

- Verify: accepts the NOT_RUN spelling as well as NOT EXECUTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R6
step("Verify: accepts the NOT_RUN spelling as well as NOT EXECUTED")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_equal(test_file_outcome_class(mk("NOT_RUN: truncated run", 0, 0, false)), "NOT_RUN")
```

</details>

#### never silently drops an error with an unrecognised class token

- Verify: never silently drops an error with an unrecognised class token


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R6
step("Verify: never silently drops an error with an unrecognised class token")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""This is the case the old prefix match counted NOWHERE."""
assert_equal(test_file_outcome_class(mk("compile error: unexpected token", 0, 0, false)), "ERROR")
```

</details>

#### reports a unit that produced no verdict at all as NOT_RUN, never OK

- Verify: reports a unit that produced no verdict at all as NOT_RUN, never OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R6
step("Verify: reports a unit that produced no verdict at all as NOT_RUN, never OK")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Exit 0 with no result line is the silent-green shape."""
assert_equal(test_file_outcome_class(mk("", 0, 0, false)), "NOT_RUN")
```

</details>

#### still reports an ordinary passing unit as OK

- Verify: still reports an ordinary passing unit as OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R6
step("Verify: still reports an ordinary passing unit as OK")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_equal(test_file_outcome_class(mk("", 0, 3, false)), "OK")
assert_equal(test_file_outcome_tag(mk("", 0, 3, false)), "PASS")
```

</details>

#### still reports an ordinary assertion failure as ERROR

- Verify: still reports an ordinary assertion failure as ERROR


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R6
step("Verify: still reports an ordinary assertion failure as ERROR")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_equal(test_file_outcome_class(mk("", 2, 1, false)), "ERROR")
assert_equal(test_file_outcome_tag(mk("", 2, 1, false)), "FAIL")
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


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `748d4970015222d1a9342fb626b0a53b0bb28b889712c6b5f73182b8874f964b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `748d4970015222d1a9342fb626b0a53b0bb28b889712c6b5f73182b8874f964b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `748d4970015222d1a9342fb626b0a53b0bb28b889712c6b5f73182b8874f964b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl
mirror: doc/06_spec/01_unit/test_runner/test_runner_output_outcome_class_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/test_runner/test_runner_output_outcome_class_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/test_runner/test_runner_output_outcome_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/test_runner_output_outcome_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
