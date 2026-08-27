# Channel Native Overflow Specification

> Tests covering Native channel overflow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Channel Native Overflow Specification

## Scenarios

### Native channel overflow

#### preserves messages beyond the old fixed native ring size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves messages beyond the old fixed native ring size


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves messages beyond the old fixed native ring size")
val channel_id = rt_channel_new()
var sent = 1
while sent <= 1100:
    rt_channel_send(channel_id, sent)
    sent = sent + 1

var received = 1
while received <= 1100:
    val value = rt_channel_try_recv(channel_id)
    if value != received:
        rt_exit(11)
    received = received + 1

rt_channel_close(channel_id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Native channel overflow.
- Native channel overflow

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
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e6c0f5e85d10ba0f27b9fde5887aaf9947c8044998742065bea81a688c90cdb0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e6c0f5e85d10ba0f27b9fde5887aaf9947c8044998742065bea81a688c90cdb0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e6c0f5e85d10ba0f27b9fde5887aaf9947c8044998742065bea81a688c90cdb0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves messages beyond the old fixed native ring size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
