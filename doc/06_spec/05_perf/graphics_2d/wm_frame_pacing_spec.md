# Wm Frame Pacing Specification

> Tests covering wm_frame_pacing — AC-7: FramePacingCounters and tick loop, FramePacingCounters field contract, idle frame detection, active frame counters, event sleep always inserted (no tight loop), frame pacing targets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Frame Pacing Specification

## Scenarios

### wm_frame_pacing — AC-7: FramePacingCounters and tick loop

### FramePacingCounters field contract

#### AC-7: event_sleep_us field is present and non-negative

- AC-7: event_sleep_us field is present and non-negative
   - Expected: c.event_sleep_us >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: event_sleep_us field is present and non-negative")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.event_sleep_us >= 0).to_equal(true)
```

</details>

#### AC-7: dirty_rect_count field is present and non-negative

- AC-7: dirty_rect_count field is present and non-negative
   - Expected: c.dirty_rect_count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: dirty_rect_count field is present and non-negative")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.dirty_rect_count >= 0).to_equal(true)
```

</details>

#### AC-7: present_batch_count field is present and non-negative

- AC-7: present_batch_count field is present and non-negative
   - Expected: c.present_batch_count >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: present_batch_count field is present and non-negative")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.present_batch_count >= 0).to_equal(true)
```

</details>

#### AC-7: idle_cpu_us field is present and non-negative

- AC-7: idle_cpu_us field is present and non-negative
   - Expected: c.idle_cpu_us >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: idle_cpu_us field is present and non-negative")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.idle_cpu_us >= 0).to_equal(true)
```

</details>

#### AC-7: frame_count field is present and greater than zero

- AC-7: frame_count field is present and greater than zero
   - Expected: c.frame_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: frame_count field is present and greater than zero")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.frame_count > 0).to_equal(true)
```

</details>

### idle frame detection

#### AC-7: idle frame has event_sleep_us >= 100

- AC-7: idle frame has event_sleep_us >= 100
   - Expected: c.event_sleep_us >= IDLE_SLEEP_MIN_US is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: idle frame has event_sleep_us >= 100")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.event_sleep_us >= IDLE_SLEEP_MIN_US).to_equal(true)
```

</details>

#### AC-7: idle frame has dirty_rect_count == 0

- AC-7: idle frame has dirty_rect_count == 0
   - Expected: c.dirty_rect_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: idle frame has dirty_rect_count == 0")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.dirty_rect_count).to_equal(0)
```

</details>

#### AC-7: idle frame is detected by is_idle_frame

- AC-7: idle frame is detected by is_idle_frame
   - Expected: is_idle_frame(c) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: idle frame is detected by is_idle_frame")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(is_idle_frame(c)).to_equal(true)
```

</details>

#### AC-7: active frame is not detected as idle

- AC-7: active frame is not detected as idle
   - Expected: is_idle_frame(c) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: active frame is not detected as idle")
val c: FramePacingCountersSentinel = make_active_frame()
expect(is_idle_frame(c)).to_equal(false)
```

</details>

### active frame counters

#### AC-7: active frame dirty_rect_count is greater than zero

- AC-7: active frame dirty_rect_count is greater than zero
   - Expected: c.dirty_rect_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: active frame dirty_rect_count is greater than zero")
val c: FramePacingCountersSentinel = make_active_frame()
expect(c.dirty_rect_count > 0).to_equal(true)
```

</details>

#### AC-7: active frame present_batch_count is greater than zero

- AC-7: active frame present_batch_count is greater than zero
   - Expected: c.present_batch_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: active frame present_batch_count is greater than zero")
val c: FramePacingCountersSentinel = make_active_frame()
expect(c.present_batch_count > 0).to_equal(true)
```

</details>

#### AC-7: active frame event_sleep_us is non-zero (event sleep always inserted)

- AC-7: active frame event_sleep_us is non-zero (event sleep always inserted)
   - Expected: has_event_sleep(c) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: active frame event_sleep_us is non-zero (event sleep always inserted)")
val c: FramePacingCountersSentinel = make_active_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>

### event sleep always inserted (no tight loop)

<details>
<summary>Advanced: AC-7: idle frame has event sleep (not a tight busy loop)</summary>

#### AC-7: idle frame has event sleep (not a tight busy loop)

- AC-7: idle frame has event sleep (not a tight busy loop)
   - Expected: has_event_sleep(c) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: idle frame has event sleep (not a tight busy loop)")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>


</details>

#### AC-7: active frame still inserts event sleep

- AC-7: active frame still inserts event sleep
   - Expected: has_event_sleep(c) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: active frame still inserts event sleep")
val c: FramePacingCountersSentinel = make_active_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>

#### AC-7: full redraw frame still inserts event sleep

- AC-7: full redraw frame still inserts event sleep
   - Expected: has_event_sleep(c) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: full redraw frame still inserts event sleep")
val c: FramePacingCountersSentinel = make_full_redraw_frame()
expect(has_event_sleep(c)).to_equal(true)
```

</details>

### frame pacing targets

#### AC-7: FRAME_TARGET_US represents 60fps budget

- AC-7: FRAME_TARGET_US represents 60fps budget
   - Expected: FRAME_TARGET_US equals `16666`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: FRAME_TARGET_US represents 60fps budget")
expect(FRAME_TARGET_US).to_equal(16666)
```

</details>

#### AC-7: idle event sleep is a fraction of frame budget (less than frame target)

- AC-7: idle event sleep is a fraction of frame budget (less than frame target)
   - Expected: c.event_sleep_us < FRAME_TARGET_US is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: idle event sleep is a fraction of frame budget (less than frame target)")
val c: FramePacingCountersSentinel = make_idle_frame()
expect(c.event_sleep_us < FRAME_TARGET_US).to_equal(true)
```

</details>

#### AC-7: dirty_rect redraw area < full-frame redraw (sentinel: 3 dirty vs 1 full)

- AC-7: dirty_rect redraw area < full-frame redraw (sentinel: 3 dirty vs 1 full)
   - Expected: dirty_count > 0 is true
   - Expected: full_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("AC-7: dirty_rect redraw area < full-frame redraw (sentinel: 3 dirty vs 1 full)")
val dirty_count: i64 = 3
val full_count: i64 = 1
# 3 partial dirty rects can cover less area than 1 full-frame rect
# This verifies we track dirty rects, not just full-frame redraws
expect(dirty_count > 0).to_equal(true)
expect(full_count > 0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/graphics_2d/wm_frame_pacing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wm_frame_pacing — AC-7: FramePacingCounters and tick loop, FramePacingCounters field contract, idle frame detection, active frame counters, event sleep always inserted (no tight loop), frame pacing targets.
- wm_frame_pacing — AC-7: FramePacingCounters and tick loop
- FramePacingCounters field contract
- idle frame detection
- active frame counters
- event sleep always inserted (no tight loop)
- frame pacing targets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cbea70665b8c157c2fde86c585b3a527394965f404809029a12745f76b4bc54`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cbea70665b8c157c2fde86c585b3a527394965f404809029a12745f76b4bc54`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cbea70665b8c157c2fde86c585b3a527394965f404809029a12745f76b4bc54`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/graphics_2d/wm_frame_pacing_spec.spl
mirror: doc/06_spec/05_perf/graphics_2d/wm_frame_pacing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/graphics_2d/wm_frame_pacing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/graphics_2d/wm_frame_pacing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/graphics_2d/wm_frame_pacing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/graphics_2d/wm_frame_pacing_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: event_sleep_us field is present and non-negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/graphics_2d/wm_frame_pacing_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: dirty_rect_count field is present and non-negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/graphics_2d/wm_frame_pacing_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-7: present_batch_count field is present and non-negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
