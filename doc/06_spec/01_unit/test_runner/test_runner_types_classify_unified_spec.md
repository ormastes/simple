# test_runner_types_classify_unified_spec

> Verifies the test runner types classify unified behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_runner_types_classify_unified_spec

Verifies the test runner types classify unified behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the test runner types classify unified behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### test_runner_types outcome classification is unified

#### classifies the with-colon and without-colon spellings identically

- Verify: classifies the with-colon and without-colon spellings identically


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: classifies the with-colon and without-colon spellings identically")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""The drift that motivated this lane: 'TERMINATED:' vs 'TERMINATED'."""
for pair in [["TERMINATED: killed by SIGTERM", "TERMINATED"],
             ["TIMEOUT: budget exceeded", "timeout"],
             ["NOT EXECUTED: never started", "not_executed"]]:
    val with_colon = test_file_result_outcome_class(mk(pair[0], 0, 0, false))
    val without = test_file_result_outcome_class(mk(pair[1], 0, 0, false))
    assert_equal(with_colon, without)
    assert_true(test_file_result_is_unverified(mk(pair[0], 0, 0, false)))
    assert_true(test_file_result_is_unverified(mk(pair[1], 0, 0, false)))
```

</details>

#### tokenises the class head so underscores and case cannot change a count

- Verify: tokenises the class head so underscores and case cannot change a count


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: tokenises the class head so underscores and case cannot change a count")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_equal(test_outcome_class_token("not_executed: nope"), "NOT EXECUTED")
assert_equal(test_outcome_class_token("  terminated : x"), "TERMINATED")
assert_equal(test_outcome_class_token(""), "")
assert_equal(test_file_result_outcome_class(mk("not_run: nope", 0, 0, false)), "NOT_RUN")
```

</details>

#### never puts an unrecognised class token in the passed bucket

- Verify: never puts an unrecognised class token in the passed bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: never puts an unrecognised class token in the passed bucket")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""A reworded producer message must fail loudly, not vanish."""
val odd = mk("WEDGED: some brand new producer message", 0, 0, false)
assert_equal(test_file_result_outcome_class(odd), "ERROR")
assert_false(odd.is_ok())
assert_false(test_file_result_is_unverified(odd))
assert_false(run_of(odd, 0, 0).is_ok())
```

</details>

#### keeps CRASHED a real failure and out of the unverified bucket

- Verify: keeps CRASHED a real failure and out of the unverified bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: keeps CRASHED a real failure and out of the unverified bucket")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val crashed = mk("CRASHED: child died by SIGSEGV", 0, 0, false)
assert_equal(test_file_result_outcome_class(crashed), "CRASHED")
assert_false(test_file_result_is_unverified(crashed))
assert_false(crashed.is_ok())
assert_false(run_of(crashed, 0, 0).is_ok())
```

</details>

#### treats a no-error no-example unit as NOT_RUN, never as a pass

- Verify: treats a no-error no-example unit as NOT_RUN, never as a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: treats a no-error no-example unit as NOT_RUN, never as a pass")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Exit 0 with no Results: line is the silent-green shape."""
val silent = mk("", 0, 0, false)
assert_equal(test_file_result_outcome_class(silent), "NOT_RUN")
assert_false(silent.is_ok())
assert_true(test_file_result_is_unverified(silent))
assert_false(run_of(silent, 0, 0).is_ok())
```

</details>

#### still reports a genuine pass as ok

- Verify: still reports a genuine pass as ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: still reports a genuine pass as ok")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ok = mk("", 3, 0, false)
assert_equal(test_file_result_outcome_class(ok), "OK")
assert_true(ok.is_ok())
assert_true(run_of(ok, 0, 0).is_ok())
```

</details>

#### gives an unrecognised-token run a non-zero exit code

- Verify: gives an unrecognised-token run a non-zero exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TESTRUNNER-R3
step("Verify: gives an unrecognised-token run a non-zero exit code")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""Unverified => 5 and UsageError => 2 per the exit-code table."""
val odd = run_of(mk("WEDGED: brand new message", 0, 0, false), 0, 0)
val code = test_run_outcome_exit_code(classify_test_run_result(odd, false))
assert_false(code == 0)
val unver = run_of(mk("TERMINATED: killed", 0, 0, false), 0, 0)
assert_equal(test_run_outcome_exit_code(classify_test_run_result(unver, false)), 5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `36b12ab8738c838dedf3f74c2a4bc93526063db9dd28fd8e10153e46e87ef542`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `36b12ab8738c838dedf3f74c2a4bc93526063db9dd28fd8e10153e46e87ef542`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `36b12ab8738c838dedf3f74c2a4bc93526063db9dd28fd8e10153e46e87ef542`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl
mirror: doc/06_spec/01_unit/test_runner/test_runner_types_classify_unified_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/test_runner/test_runner_types_classify_unified_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/test_runner/test_runner_types_classify_unified_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/test_runner_types_classify_unified_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
