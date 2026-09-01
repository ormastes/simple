# Crash Classification Specification

> Tests covering crashed specs are classified separately from failures and timeouts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crash Classification Specification

## Scenarios

### crashed specs are classified separately from failures and timeouts

#### reports a signal death (no exit code) as CRASHED, not a plain failure

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports a signal death (no exit code) as CRASHED, not a plain failure
   - Expected: r.error.starts_with("CRASHED") is true
   - Expected: r.timed_out is false
   - Expected: r.failed equals `1`
   - Expected: r.passed equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a signal death (no exit code) as CRASHED, not a plain failure")
# Reproducing case: the runtime maps death-by-signal onto exit_code -1,
# the same sentinel as a timeout. Without the CRASHED branch this read
# as "Process exited with code -1".
val r = make_result_from_output("x_spec.spl", "", "fatal runtime error: stack overflow, aborting", -1, 10, 60)
expect(r.error.starts_with("CRASHED")).to_equal(true)
expect(r.timed_out).to_equal(false)
expect(r.failed).to_equal(1)
expect(r.passed).to_equal(0)
```

</details>

#### still reports a timeout as timed out, not as a crash

- still reports a timeout as timed out, not as a crash
   - Expected: r.timed_out is true
   - Expected: r.error.starts_with("CRASHED") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still reports a timeout as timed out, not as a crash")
# Similar-problem detection: the two share the -1 sentinel, so a
# classification bug in either direction shows up here.
val r = make_result_from_output("y_spec.spl", "", "TIMEOUT", -1, 10, 60)
expect(r.timed_out).to_equal(true)
expect(r.error.starts_with("CRASHED")).to_equal(false)
```

</details>

#### leaves an ordinary non-zero exit as an ordinary failure

- leaves an ordinary non-zero exit as an ordinary failure
   - Expected: r.error.starts_with("CRASHED") is false
   - Expected: r.failed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("leaves an ordinary non-zero exit as an ordinary failure")
val r = make_result_from_output("z_spec.spl", "1 example, 1 failure", "", 1, 10, 60)
expect(r.error.starts_with("CRASHED")).to_equal(false)
expect(r.failed).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/crash_classification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering crashed specs are classified separately from failures and timeouts.
- crashed specs are classified separately from failures and timeouts

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fb248d443404bac2dab240e288139e39ff0f543f50a77c3c8cce74098735e360`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fb248d443404bac2dab240e288139e39ff0f543f50a77c3c8cce74098735e360`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fb248d443404bac2dab240e288139e39ff0f543f50a77c3c8cce74098735e360`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/test_runner/crash_classification_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/crash_classification_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/crash_classification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/crash_classification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/crash_classification_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/test_runner/crash_classification_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports a signal death (no exit code) as CRASHED, not a plain failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/crash_classification_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still reports a timeout as timed out, not as a crash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/crash_classification_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves an ordinary non-zero exit as an ordinary failure' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
