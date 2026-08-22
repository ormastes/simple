# test_runner_output_class_boundary_spec

> Verifies the test runner output class boundary behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_runner_output_class_boundary_spec

Verifies the test runner output class boundary behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the test runner output class boundary behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### test_runner_output outcome class boundaries

#### keeps CRASHED distinct from TERMINATED

- Verify: keeps CRASHED distinct from TERMINATED


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: keeps CRASHED distinct from TERMINATED")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: keeps TIMEOUT distinct from TERMINATED even though both are unverified


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: keeps TIMEOUT distinct from TERMINATED even though both are unverified")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_equal(test_file_outcome_class(mk("TIMEOUT: exceeded the per-unit budget", 0, false)), "TIMEOUT")
assert_equal(test_file_outcome_class(mk("TERMINATED: killed by signal", 0, false)), "TERMINATED")
```

</details>

#### never tags an unverified unit as a pass or a plain failure

- Verify: never tags an unverified unit as a pass or a plain failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: never tags an unverified unit as a pass or a plain failure")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""rc=143/144 is UNVERIFIED: neither PASS nor FAIL."""
for err in ["TERMINATED: killed by SIGTERM", "TIMEOUT: budget exceeded"]:
    val tag = test_file_outcome_tag(mk(err, 0, false))
    assert_false(tag == "PASS")
    assert_false(tag == "FAIL")
```

</details>

#### does not let the timed_out struct flag reclassify a CRASHED unit

- Verify: does not let the timed_out struct flag reclassify a CRASHED unit


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: does not let the timed_out struct flag reclassify a CRASHED unit")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""The error class token wins over the flag, so a crash cannot be
laundered into the unverified bucket."""
assert_equal(test_file_outcome_class(mk("CRASHED: child died by signal", 1, true)), "CRASHED")
```

</details>

#### classifies a bare timed_out flag with no error text as TIMEOUT, not OK

- Verify: classifies a bare timed_out flag with no error text as TIMEOUT, not OK


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: classifies a bare timed_out flag with no error text as TIMEOUT, not OK")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_equal(test_file_outcome_class(mk("", 0, true)), "TIMEOUT")
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


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `06a304de502364db87e75b974af22ab90352fe0df569d70f7ddcc6b7550f39dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `06a304de502364db87e75b974af22ab90352fe0df569d70f7ddcc6b7550f39dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `06a304de502364db87e75b974af22ab90352fe0df569d70f7ddcc6b7550f39dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/test_runner/test_runner_output_class_boundary_spec.spl
mirror: doc/06_spec/01_unit/test_runner/test_runner_output_class_boundary_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/test_runner/test_runner_output_class_boundary_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/test_runner/test_runner_output_class_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/test_runner_output_class_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
