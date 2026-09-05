# Semihost Capture Sleep Ms Specification

> Tests covering sleep_ms sub-second durations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Semihost Capture Sleep Ms Specification

## Scenarios

### sleep_ms sub-second durations

#### actually blocks for sub-second millisecond values (300ms)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- actually blocks for sub-second millisecond values (300ms)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("actually blocks for sub-second millisecond values (300ms)")
val start = now_ms()
sleep_ms(300)
val elapsed = now_ms() - start
# Old buggy code: seconds = 300 / 1000 = 0 -> no sleep -> elapsed ~0ms.
# Fixed code should block for close to 300ms (allow generous slack
# for process-spawn overhead / CI jitter, but must be well above the
# near-zero elapsed time the bug produced).
expect(elapsed).to_be_greater_than(150)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sleep_ms sub-second durations.
- sleep_ms sub-second durations

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
- `REQ-EXEC-SEMIHOST-SLEEP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8d32ef0bca8d53082817a3cf20c560f636a425322f3f7d944cb7bb423b016fc3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8d32ef0bca8d53082817a3cf20c560f636a425322f3f7d944cb7bb423b016fc3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8d32ef0bca8d53082817a3cf20c560f636a425322f3f7d944cb7bb423b016fc3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=89; blocker cap makes effective=49
doc/06_spec/unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/nogc_async_mut_noalloc/execution/semihost_capture_sleep_ms_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'actually blocks for sub-second millisecond values (300ms)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
