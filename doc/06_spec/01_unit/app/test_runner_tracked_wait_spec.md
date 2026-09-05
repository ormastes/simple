# Test Runner Tracked Wait Specification

> Tests covering tracked test child wait.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Tracked Wait Specification

## Scenarios

### tracked test child wait

#### kills and untracks a timed-out child

- kills and untracks a timed-out child
   - Expected: wait_tracked_process(pid, 10) equals `-1`
   - Expected: process_is_running(pid) is false
   - Expected: tracker_get_pids().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("kills and untracks a timed-out child")
if host_os() == "windows":
    return
tracker_clear()
val pid = spawn_tracked_process("/bin/sh", ["-c", "sleep 5"])
expect(pid).to_be_greater_than(0)
expect(wait_tracked_process(pid, 10)).to_equal(-1)
expect(process_is_running(pid)).to_equal(false)
expect(tracker_get_pids().len()).to_equal(0)
```

</details>

#### retains the observed exit code when polling completes

- retains the observed exit code when polling completes
   - Expected: exit_code equals `7`
   - Expected: tracker_get_pids().len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("retains the observed exit code when polling completes")
if host_os() == "windows":
    return
tracker_clear()
val pid = spawn_tracked_process("/bin/sh", ["-c", "exit 7"])
var exit_code: i64 = -2
var attempts = 0
while exit_code == -2 and attempts < 100:
    exit_code = poll_tracked_process(pid)
    attempts = attempts + 1
expect(exit_code).to_equal(7)
expect(tracker_get_pids().len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_tracked_wait_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tracked test child wait.
- tracked test child wait

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4f47e28a4903744881589d0456e86ba3c43d861365d9788e3d0b685803332388`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4f47e28a4903744881589d0456e86ba3c43d861365d9788e3d0b685803332388`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4f47e28a4903744881589d0456e86ba3c43d861365d9788e3d0b685803332388`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/test_runner_tracked_wait_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_tracked_wait_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_tracked_wait_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_tracked_wait_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_tracked_wait_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_tracked_wait_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'kills and untracks a timed-out child' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_tracked_wait_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the observed exit code when polling completes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
