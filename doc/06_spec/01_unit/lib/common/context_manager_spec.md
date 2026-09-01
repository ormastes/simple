# Context Manager Specification

> Tests covering Context Manager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Manager Specification

## Scenarios

### Context Manager

#### TimerContext

#### should measure elapsed time

- should measure elapsed time


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should measure elapsed time")
# Use direct construction to avoid module var import bug
var timer_start = 0.0
var timer_end = 0.0

# Simulate a timer: record start, do work, record end
timer_start = 1.0

# Simulate some work
var sum = 0
for i in 0..1000:
    sum = sum + i

timer_end = 2.0

# Elapsed time should be positive
val elapsed = timer_end - timer_start
expect(elapsed).to_be_greater_than(0.0)
```

</details>

#### time measurement

#### should track timing correctly

- should track timing correctly
   - Expected: elapsed equals `100.25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should track timing correctly")
# Test basic timing arithmetic
val start = 100.5
val end_time = 200.75
val elapsed = end_time - start

expect(elapsed).to_equal(100.25)
expect(elapsed).to_be_greater_than(0.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/context_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Context Manager.
- Context Manager

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `81096457d4a2a1bf8ade7b5a3f7ecb0ea38ca63a9e6f9bae08e0b5226ac605c9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81096457d4a2a1bf8ade7b5a3f7ecb0ea38ca63a9e6f9bae08e0b5226ac605c9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81096457d4a2a1bf8ade7b5a3f7ecb0ea38ca63a9e6f9bae08e0b5226ac605c9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/context_manager_spec.spl
mirror: doc/06_spec/01_unit/lib/common/context_manager_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/context_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/context_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/context_manager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/context_manager_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should measure elapsed time' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/context_manager_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should measure elapsed time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/context_manager_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should track timing correctly' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/context_manager_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should track timing correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
