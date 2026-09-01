# Runtime Timer Sleep Specification

> Tests covering Runtime timer sleep basics, Runtime timer sleep concurrency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Runtime Timer Sleep Specification

## Scenarios

### Runtime timer sleep basics

#### a 40ms runtime sleep task completes and takes at least 40ms

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- a 40ms runtime sleep task completes and takes at least 40ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a 40ms runtime sleep task completes and takes at least 40ms")
val rt = Runtime.new()
val tid = rt.spawn_sleep(40)
val t0 = time_now_unix_micros()
rt.run()
val elapsed_us = time_now_unix_micros() - t0
assert_false(rt.tasks.contains_key(tid))
assert_true(elapsed_us >= 40000)
```

</details>

#### spawn_sleep(0) completes promptly

- spawn_sleep(0) completes promptly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawn_sleep(0) completes promptly")
val rt = Runtime.new()
val tid = rt.spawn_sleep(0)
val t0 = time_now_unix_micros()
rt.run()
val elapsed_us = time_now_unix_micros() - t0
assert_false(rt.tasks.contains_key(tid))
assert_true(elapsed_us < 1000000)
```

</details>

### Runtime timer sleep concurrency

#### two overlapping 60ms runtime sleeps finish well under the 120ms sum

- two overlapping 60ms runtime sleeps finish well under the 120ms sum


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two overlapping 60ms runtime sleeps finish well under the 120ms sum")
val rt = Runtime.new()
val a = rt.spawn_sleep(60)
val b = rt.spawn_sleep(60)
val t0 = time_now_unix_micros()
rt.run()
val elapsed_us = time_now_unix_micros() - t0
assert_false(rt.tasks.contains_key(a))
assert_false(rt.tasks.contains_key(b))
assert_true(elapsed_us >= 60000)
assert_true(elapsed_us < 110000)
```

</details>

#### nearest-deadline parking: 20ms and 80ms runtime sleeps finish in ~80ms

- nearest-deadline parking: 20ms and 80ms runtime sleeps finish in ~80ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nearest-deadline parking: 20ms and 80ms runtime sleeps finish in ~80ms")
val rt = Runtime.new()
rt.spawn_sleep(80)
rt.spawn_sleep(20)
val t0 = time_now_unix_micros()
rt.run()
val elapsed_us = time_now_unix_micros() - t0
assert_true(elapsed_us >= 80000)
assert_true(elapsed_us < 160000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/async/runtime_timer_sleep_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Runtime timer sleep basics, Runtime timer sleep concurrency.
- Runtime timer sleep basics
- Runtime timer sleep concurrency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `9a28d2ca4e04f601018cc46480dbeb0564622cdcf61a030e2c5bed3fb8ee42a2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a28d2ca4e04f601018cc46480dbeb0564622cdcf61a030e2c5bed3fb8ee42a2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a28d2ca4e04f601018cc46480dbeb0564622cdcf61a030e2c5bed3fb8ee42a2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/async/runtime_timer_sleep_spec.spl
mirror: doc/06_spec/01_unit/lib/async/runtime_timer_sleep_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/async/runtime_timer_sleep_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/async/runtime_timer_sleep_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/async/runtime_timer_sleep_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a 40ms runtime sleep task completes and takes at least 40ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/async/runtime_timer_sleep_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spawn_sleep(0) completes promptly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/async/runtime_timer_sleep_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'two overlapping 60ms runtime sleeps finish well under the 120ms sum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
