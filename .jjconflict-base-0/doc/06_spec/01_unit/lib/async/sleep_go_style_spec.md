# Sleep Go Style Specification

> Tests covering Go-style sleep basics, Go-style sleep concurrency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sleep Go Style Specification

## Scenarios

### Go-style sleep basics

#### sleep(0) is immediately ready and await returns

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sleep(0) is immediately ready and await returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep(0) is immediately ready and await returns")
val s = sleep(0)
await_sleep(s)
val p = s.poll()
var ready = false
match p:
    case Poll.Ready(_):
        ready = true
    case Poll.Pending:
        ready = false
assert_true(ready)
```

</details>

#### fresh sleep(N) is pending before its deadline

- fresh sleep(N) is pending before its deadline


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fresh sleep(N) is pending before its deadline")
val s = sleep(5000)
val p = s.poll()
var pending = false
match p:
    case Poll.Ready(_):
        pending = false
    case Poll.Pending:
        pending = true
assert_true(pending)
```

</details>

#### awaiting sleep(N ms) takes at least N ms

- awaiting sleep(N ms) takes at least N ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("awaiting sleep(N ms) takes at least N ms")
val t0 = time_now_unix_micros()
val s = sleep(30)
await_sleep(s)
val elapsed_us = time_now_unix_micros() - t0
assert_true(elapsed_us >= 30000)
```

</details>

#### sleep_blocking(0) returns without blocking

- sleep_blocking(0) returns without blocking


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sleep_blocking(0) returns without blocking")
val t0 = time_now_unix_micros()
sleep_blocking(0)
val elapsed_us = time_now_unix_micros() - t0
assert_true(elapsed_us < 5000000)
```

</details>

### Go-style sleep concurrency

#### two concurrent 60ms sleeps overlap (total well under the 120ms sum)

- two concurrent 60ms sleeps overlap (total well under the 120ms sum)


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two concurrent 60ms sleeps overlap (total well under the 120ms sum)")
val t0 = time_now_unix_micros()
val a = sleep(60)
val b = sleep(60)
run_sleepers([a, b])
val elapsed_us = time_now_unix_micros() - t0
# Both elapsed (correctness) ...
assert_true(a.is_elapsed())
assert_true(b.is_elapsed())
# ... at least one full sleep passed ...
assert_true(elapsed_us >= 60000)
# ... and the sleeps overlapped: far below the 120ms serial sum.
assert_true(elapsed_us < 110000)
```

</details>

#### nearest-deadline parking: 20ms and 80ms sleepers finish in ~80ms

- nearest-deadline parking: 20ms and 80ms sleepers finish in ~80ms


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nearest-deadline parking: 20ms and 80ms sleepers finish in ~80ms")
val t0 = time_now_unix_micros()
run_sleepers([sleep(80), sleep(20)])
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
| Source | `test/01_unit/lib/async/sleep_go_style_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Go-style sleep basics, Go-style sleep concurrency.
- Go-style sleep basics
- Go-style sleep concurrency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `3de114640ac6d07612ec08b034a77525d4ae6d74b185f462217b1d0dc8db963e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3de114640ac6d07612ec08b034a77525d4ae6d74b185f462217b1d0dc8db963e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3de114640ac6d07612ec08b034a77525d4ae6d74b185f462217b1d0dc8db963e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/async/sleep_go_style_spec.spl
mirror: doc/06_spec/01_unit/lib/async/sleep_go_style_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/async/sleep_go_style_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/async/sleep_go_style_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/async/sleep_go_style_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sleep(0) is immediately ready and await returns' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/async/sleep_go_style_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fresh sleep(N) is pending before its deadline' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/async/sleep_go_style_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'awaiting sleep(N ms) takes at least N ms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
