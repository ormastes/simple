# Browser App Idle Poll Specification

> Tests covering browser app idle file polling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser App Idle Poll Specification

## Scenarios

### browser app idle file polling

#### throttles idle file change checks but polls immediately after events

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- throttles idle file change checks but polls immediately after events
   - Expected: poll1 is false
   - Expected: ticks1 equals `1`
   - Expected: poll2 is false
   - Expected: ticks2 equals `2`
   - Expected: poll3 is true
   - Expected: ticks3 equals `0`
   - Expected: poll4 is true
   - Expected: ticks4 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("throttles idle file change checks but polls immediately after events")
val (poll1, ticks1) = browser_file_change_poll_next(false, 0, 3)
expect(poll1).to_equal(false)
expect(ticks1).to_equal(1)

val (poll2, ticks2) = browser_file_change_poll_next(false, ticks1, 3)
expect(poll2).to_equal(false)
expect(ticks2).to_equal(2)

val (poll3, ticks3) = browser_file_change_poll_next(false, ticks2, 3)
expect(poll3).to_equal(true)
expect(ticks3).to_equal(0)

val (poll4, ticks4) = browser_file_change_poll_next(true, 2, 3)
expect(poll4).to_equal(true)
expect(ticks4).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui/browser_app_idle_poll_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering browser app idle file polling.
- browser app idle file polling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `f69e1fb73f218d71e84103cb381e5356e5eb7d74e6bef1eaab74d454ae9290d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f69e1fb73f218d71e84103cb381e5356e5eb7d74e6bef1eaab74d454ae9290d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f69e1fb73f218d71e84103cb381e5356e5eb7d74e6bef1eaab74d454ae9290d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/app/ui/browser_app_idle_poll_spec.spl
mirror: doc/06_spec/unit/app/ui/browser_app_idle_poll_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/browser_app_idle_poll_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/browser_app_idle_poll_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/browser_app_idle_poll_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/ui/browser_app_idle_poll_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'throttles idle file change checks but polls immediately after events' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
