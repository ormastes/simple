# Test Runner Output Class Boundary Specification

> Tests covering test_runner_output outcome class boundaries.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Output Class Boundary Specification

## Scenarios

### test_runner_output outcome class boundaries

#### keeps CRASHED distinct from TERMINATED

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps CRASHED distinct from TERMINATED


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("keeps CRASHED distinct from TERMINATED")
val crashed = mk("CRASHED: fork child died by SIGSEGV", 1, false)
val terminated = mk("TERMINATED: fork child killed by SIGTERM (unverified)", 0, false)
assert_equal(test_file_outcome_class(crashed), "CRASHED")
assert_equal(test_file_outcome_class(terminated), "TERMINATED")
assert_false(test_file_outcome_class(crashed) == test_file_outcome_class(terminated))
assert_equal(test_file_outcome_tag(crashed), "CRASH")
assert_equal(test_file_outcome_tag(terminated), "TERM")
```

</details>

#### keeps TIMEOUT distinct from TERMINATED even though both are unverified

- keeps TIMEOUT distinct from TERMINATED even though both are unverified


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("keeps TIMEOUT distinct from TERMINATED even though both are unverified")
assert_equal(test_file_outcome_class(mk("TIMEOUT: exceeded the per-unit budget", 0, false)), "TIMEOUT")
assert_equal(test_file_outcome_class(mk("TERMINATED: killed by signal", 0, false)), "TERMINATED")
```

</details>

#### never tags an unverified unit as a pass or a plain failure

- never tags an unverified unit as a pass or a plain failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("never tags an unverified unit as a pass or a plain failure")
"""rc=143/144 is UNVERIFIED: neither PASS nor FAIL."""
for err in ["TERMINATED: killed by SIGTERM", "TIMEOUT: budget exceeded"]:
    val tag = test_file_outcome_tag(mk(err, 0, false))
    assert_false(tag == "PASS")
    assert_false(tag == "FAIL")
```

</details>

#### does not let the timed_out struct flag reclassify a CRASHED unit

- does not let the timed_out struct flag reclassify a CRASHED unit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("does not let the timed_out struct flag reclassify a CRASHED unit")
"""The error class token wins over the flag, so a crash cannot be
laundered into the unverified bucket."""
assert_equal(test_file_outcome_class(mk("CRASHED: child died by signal", 1, true)), "CRASHED")
```

</details>

#### classifies a bare timed_out flag with no error text as TIMEOUT, not OK

- classifies a bare timed_out flag with no error text as TIMEOUT, not OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("classifies a bare timed_out flag with no error text as TIMEOUT, not OK")
assert_equal(test_file_outcome_class(mk("", 0, true)), "TIMEOUT")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test_runner_output outcome class boundaries.
- test_runner_output outcome class boundaries

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-TESTRUNNER-R3`
- `REQ-SSPEC-TEST_RUNNER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8c5dd4c2696b9a4e9d6167c67126eca76695b7a41e2728d7fbf033752713e040`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8c5dd4c2696b9a4e9d6167c67126eca76695b7a41e2728d7fbf033752713e040`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8c5dd4c2696b9a4e9d6167c67126eca76695b7a41e2728d7fbf033752713e040`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl
mirror: doc/06_spec/01_unit/test_runner/test_runner_output_class_boundary_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/test_runner/test_runner_output_class_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/test_runner_output_class_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps CRASHED distinct from TERMINATED' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps TIMEOUT distinct from TERMINATED even though both are unverified' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never tags an unverified unit as a pass or a plain failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
