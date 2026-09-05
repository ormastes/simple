# Process Run Timeout Live Group Kill Specification

> Tests covering process_run_timeout_live.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Run Timeout Live Group Kill Specification

## Scenarios

### process_run_timeout_live

#### does not time out a 2 s worker under a 60 s budget

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not time out a 2 s worker under a 60 s budget
   - Expected: code equals `0`
   - Expected: err does not contain `[TIMEOUT:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("does not time out a 2 s worker under a 60 s budget")
val (_out, err, code) = process_run_timeout_live("sleep", ["2"], 60000)
expect(code).to_equal(0)
expect(err.contains("[TIMEOUT:")).to_equal(false)
```

</details>

#### times out a 3 s worker under a 1 s budget with the marker

- times out a 3 s worker under a 1 s budget with the marker
   - Expected: code equals `-1`
   - Expected: err contains `[TIMEOUT:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("times out a 3 s worker under a 1 s budget with the marker")
val (_out, err, code) = process_run_timeout_live("sleep", ["3"], 1000)
expect(code).to_equal(-1)
expect(err.contains("[TIMEOUT:")).to_equal(true)
```

</details>

#### terminates the whole worker tree when the worker exits non-zero

- terminates the whole worker tree when the worker exits non-zero
   - Expected: code equals `3`
   - Expected: err does not contain `[TIMEOUT:`
   - Expected: survivors(tag) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("terminates the whole worker tree when the worker exits non-zero")
# A worker that leaves a background grandchild behind and fails: the
# grandchild must not outlive the call (run6 orphan shape).
val tag = "sleep 37.0731"
val (_out, err, code) = process_run_timeout_live("sh", ["-c", "{tag} & exit 3"], 60000)
expect(code).to_equal(3)
expect(err.contains("[TIMEOUT:")).to_equal(false)
expect(survivors(tag)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/process_run_timeout_live_group_kill_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering process_run_timeout_live.
- process_run_timeout_live

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c7977f0b60d7a38c06972448cffb8307c8a31ade57b6351f9784e916db06ad89`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7977f0b60d7a38c06972448cffb8307c8a31ade57b6351f9784e916db06ad89`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7977f0b60d7a38c06972448cffb8307c8a31ade57b6351f9784e916db06ad89`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/io/process_run_timeout_live_group_kill_spec.spl
mirror: doc/06_spec/01_unit/app/io/process_run_timeout_live_group_kill_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/process_run_timeout_live_group_kill_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/process_run_timeout_live_group_kill_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/process_run_timeout_live_group_kill_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/io/process_run_timeout_live_group_kill_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not time out a 2 s worker under a 60 s budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/process_run_timeout_live_group_kill_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'times out a 3 s worker under a 1 s budget with the marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/process_run_timeout_live_group_kill_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'terminates the whole worker tree when the worker exits non-zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
