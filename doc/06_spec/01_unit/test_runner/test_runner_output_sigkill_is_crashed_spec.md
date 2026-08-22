# test_runner_output_sigkill_is_crashed_spec

> Verifies the test runner output sigkill is crashed behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_runner_output_sigkill_is_crashed_spec

Verifies the test runner output sigkill is crashed behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/test_runner_output_sigkill_is_crashed_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the test runner output sigkill is crashed behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### fork exit signal attribution

#### does not treat SIGKILL as an outside kill

- Verify: does not treat SIGKILL as an outside kill


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: does not treat SIGKILL as an outside kill")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""9 must fall through to the CRASHED branch."""
assert_false(is_outside_kill(9))
```

</details>

#### still treats SIGTERM, SIGINT and SIGHUP as outside kills

- Verify: still treats SIGTERM, SIGINT and SIGHUP as outside kills


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: still treats SIGTERM, SIGINT and SIGHUP as outside kills")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_true(is_outside_kill(15))
assert_true(is_outside_kill(2))
assert_true(is_outside_kill(1))
```

</details>

#### still treats fault signals as the program's own defect

- Verify: still treats fault signals as the program's own defect


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: still treats fault signals as the program's own defect")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_false(is_outside_kill(11))
assert_false(is_outside_kill(6))
assert_false(is_outside_kill(4))
assert_false(is_outside_kill(7))
assert_false(is_outside_kill(8))
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


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `043337da12439b6d68bac850a781abc39a7b020aef22cbc5273b697eda8186cc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `043337da12439b6d68bac850a781abc39a7b020aef22cbc5273b697eda8186cc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `043337da12439b6d68bac850a781abc39a7b020aef22cbc5273b697eda8186cc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/test_runner/test_runner_output_sigkill_is_crashed_spec.spl
mirror: doc/06_spec/01_unit/test_runner/test_runner_output_sigkill_is_crashed_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/test_runner/test_runner_output_sigkill_is_crashed_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/test_runner/test_runner_output_sigkill_is_crashed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/test_runner_output_sigkill_is_crashed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
