# Truncated Capture Fail Closed Specification

> Tests covering truncated capture is never a clean pass, detection: the guard must key on truncation, not on anything else.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Truncated Capture Fail Closed Specification

## Scenarios

### truncated capture is never a clean pass

#### reports a failure when the truncation marker is present

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a failure when the truncation marker is present


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a failure when the truncation marker is present")
val r = make_result_from_output("x_spec.spl", _truncated_stdout(), "", 0, 10, 60)
assert_true(r.failed > 0)
```

</details>

#### names truncation in the error so the cause is not guessed

- names truncation in the error so the cause is not guessed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("names truncation in the error so the cause is not guessed")
val r = make_result_from_output("x_spec.spl", _truncated_stdout(), "", 0, 10, 60)
assert_true(r.error.contains("truncat"))
```

</details>

#### does not credit the scraped pass count from a truncated capture

- does not credit the scraped pass count from a truncated capture


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not credit the scraped pass count from a truncated capture")
val r = make_result_from_output("x_spec.spl", _truncated_stdout(), "", 0, 10, 60)
assert_equal(r.passed, 0)
```

</details>

### detection: the guard must key on truncation, not on anything else

#### an untruncated green capture still passes

- an untruncated green capture still passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an untruncated green capture still passes")
val r = make_result_from_output("x_spec.spl", _clean_stdout(), "", 0, 10, 60)
assert_equal(r.passed, 12)
assert_equal(r.failed, 0)
```

</details>

#### a marker on stderr is caught too

- a marker on stderr is caught too


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a marker on stderr is caught too")
val r = make_result_from_output("x_spec.spl", _clean_stdout(), "[output truncated: 99 bytes omitted]", 0, 10, 60)
assert_true(r.failed > 0)
```

</details>

#### a marker with a different omitted-byte count is still caught

- a marker with a different omitted-byte count is still caught


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a marker with a different omitted-byte count is still caught")
val out = "Passed: 3\nFailed: 0\n[output truncated: 1 bytes omitted]\n"
val r = make_result_from_output("x_spec.spl", out, "", 0, 10, 60)
assert_true(r.failed > 0)
```

</details>

#### prose merely mentioning truncation is not enough to fail a file

- prose merely mentioning truncation is not enough to fail a file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prose merely mentioning truncation is not enough to fail a file")
val out = "Passed: 3\nFailed: 0\nnote: we discuss output truncated behaviour here\n"
val r = make_result_from_output("x_spec.spl", out, "", 0, 10, 60)
assert_equal(r.failed, 0)
assert_equal(r.passed, 3)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering truncated capture is never a clean pass, detection: the guard must key on truncation, not on anything else.
- truncated capture is never a clean pass
- detection: the guard must key on truncation, not on anything else

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2126778764deaf0e17271a5556f59bca6a1667ee3fc2fb06883f80a8ae29d81d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2126778764deaf0e17271a5556f59bca6a1667ee3fc2fb06883f80a8ae29d81d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2126778764deaf0e17271a5556f59bca6a1667ee3fc2fb06883f80a8ae29d81d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a failure when the truncation marker is present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names truncation in the error so the cause is not guessed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/truncated_capture_fail_closed_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not credit the scraped pass count from a truncated capture' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
