# Test Runner Output Outcome Class Specification

> Tests covering test_runner_output outcome classification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Output Outcome Class Specification

## Scenarios

### test_runner_output outcome classification

#### classifies on the class token, not on the message wording

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies on the class token, not on the message wording


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("classifies on the class token, not on the message wording")
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

- accepts the NOT_RUN spelling as well as NOT EXECUTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("accepts the NOT_RUN spelling as well as NOT EXECUTED")
assert_equal(test_file_outcome_class(mk("NOT_RUN: truncated run", 0, 0, false)), "NOT_RUN")
```

</details>

#### never silently drops an error with an unrecognised class token

- never silently drops an error with an unrecognised class token


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("never silently drops an error with an unrecognised class token")
"""This is the case the old prefix match counted NOWHERE."""
assert_equal(test_file_outcome_class(mk("compile error: unexpected token", 0, 0, false)), "ERROR")
```

</details>

#### reports a unit that produced no verdict at all as NOT_RUN, never OK

- reports a unit that produced no verdict at all as NOT_RUN, never OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("reports a unit that produced no verdict at all as NOT_RUN, never OK")
"""Exit 0 with no result line is the silent-green shape."""
assert_equal(test_file_outcome_class(mk("", 0, 0, false)), "NOT_RUN")
```

</details>

#### still reports an ordinary passing unit as OK

- still reports an ordinary passing unit as OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("still reports an ordinary passing unit as OK")
assert_equal(test_file_outcome_class(mk("", 0, 3, false)), "OK")
assert_equal(test_file_outcome_tag(mk("", 0, 3, false)), "PASS")
```

</details>

#### still reports an ordinary assertion failure as ERROR

- still reports an ordinary assertion failure as ERROR


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("still reports an ordinary assertion failure as ERROR")
assert_equal(test_file_outcome_class(mk("", 2, 1, false)), "ERROR")
assert_equal(test_file_outcome_tag(mk("", 2, 1, false)), "FAIL")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test_runner_output outcome classification.
- test_runner_output outcome classification

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-TESTRUNNER-R6`
- `REQ-SSPEC-TEST_RUNNER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f7ac3656c0135e187c1a812f162b840e5c417d10b8571007aeb362ed6a1f330d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7ac3656c0135e187c1a812f162b840e5c417d10b8571007aeb362ed6a1f330d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7ac3656c0135e187c1a812f162b840e5c417d10b8571007aeb362ed6a1f330d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl
mirror: doc/06_spec/01_unit/test_runner/test_runner_output_outcome_class_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/test_runner/test_runner_output_outcome_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/test_runner_output_outcome_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies on the class token, not on the message wording' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the NOT_RUN spelling as well as NOT EXECUTED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/test_runner_output_outcome_class_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never silently drops an error with an unrecognised class token' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
