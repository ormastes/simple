# Test Runner Types Classify Unified Specification

> Tests covering test_runner_types outcome classification is unified.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Types Classify Unified Specification

## Scenarios

### test_runner_types outcome classification is unified

#### classifies the with-colon and without-colon spellings identically

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- classifies the with-colon and without-colon spellings identically


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("classifies the with-colon and without-colon spellings identically")
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

- tokenises the class head so underscores and case cannot change a count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("tokenises the class head so underscores and case cannot change a count")
assert_equal(test_outcome_class_token("not_executed: nope"), "NOT EXECUTED")
assert_equal(test_outcome_class_token("  terminated : x"), "TERMINATED")
assert_equal(test_outcome_class_token(""), "")
assert_equal(test_file_result_outcome_class(mk("not_run: nope", 0, 0, false)), "NOT_RUN")
```

</details>

#### never puts an unrecognised class token in the passed bucket

- never puts an unrecognised class token in the passed bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("never puts an unrecognised class token in the passed bucket")
"""A reworded producer message must fail loudly, not vanish."""
val odd = mk("WEDGED: some brand new producer message", 0, 0, false)
assert_equal(test_file_result_outcome_class(odd), "ERROR")
assert_false(odd.is_ok())
assert_false(test_file_result_is_unverified(odd))
assert_false(run_of(odd, 0, 0).is_ok())
```

</details>

#### keeps CRASHED a real failure and out of the unverified bucket

- keeps CRASHED a real failure and out of the unverified bucket


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("keeps CRASHED a real failure and out of the unverified bucket")
val crashed = mk("CRASHED: child died by SIGSEGV", 0, 0, false)
assert_equal(test_file_result_outcome_class(crashed), "CRASHED")
assert_false(test_file_result_is_unverified(crashed))
assert_false(crashed.is_ok())
assert_false(run_of(crashed, 0, 0).is_ok())
```

</details>

#### treats a no-error no-example unit as NOT_RUN, never as a pass

- treats a no-error no-example unit as NOT_RUN, never as a pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("treats a no-error no-example unit as NOT_RUN, never as a pass")
"""Exit 0 with no Results: line is the silent-green shape."""
val silent = mk("", 0, 0, false)
assert_equal(test_file_result_outcome_class(silent), "NOT_RUN")
assert_false(silent.is_ok())
assert_true(test_file_result_is_unverified(silent))
assert_false(run_of(silent, 0, 0).is_ok())
```

</details>

#### still reports a genuine pass as ok

- still reports a genuine pass as ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("still reports a genuine pass as ok")
val ok = mk("", 3, 0, false)
assert_equal(test_file_result_outcome_class(ok), "OK")
assert_true(ok.is_ok())
assert_true(run_of(ok, 0, 0).is_ok())
```

</details>

#### gives an unrecognised-token run a non-zero exit code

- gives an unrecognised-token run a non-zero exit code


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-TEST_RUNNER
step("gives an unrecognised-token run a non-zero exit code")
"""Unverified => 5 and UsageError => 2 per the exit-code table."""
val odd = run_of(mk("WEDGED: brand new message", 0, 0, false), 0, 0)
val code = test_run_outcome_exit_code(classify_test_run_result(odd, false))
assert_false(code == 0)
val unver = run_of(mk("TERMINATED: killed", 0, 0, false), 0, 0)
assert_equal(test_run_outcome_exit_code(classify_test_run_result(unver, false)), 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test_runner_types outcome classification is unified.
- test_runner_types outcome classification is unified

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `a91c55ea0f07b1c39b7c239a9f1f36ecd9e0df1abf3cc837b78ce1a0cc915f20`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a91c55ea0f07b1c39b7c239a9f1f36ecd9e0df1abf3cc837b78ce1a0cc915f20`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a91c55ea0f07b1c39b7c239a9f1f36ecd9e0df1abf3cc837b78ce1a0cc915f20`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl
mirror: doc/06_spec/01_unit/test_runner/test_runner_types_classify_unified_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/test_runner/test_runner_types_classify_unified_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/test_runner/test_runner_types_classify_unified_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'classifies the with-colon and without-colon spellings identically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tokenises the class head so underscores and case cannot change a count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/test_runner/test_runner_types_classify_unified_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never puts an unrecognised class token in the passed bucket' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
