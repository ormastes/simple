# FrameClock Port Spec

> `FrameClock` is the portable time seam for the WM/GUI/web/2D lane (tranche W1 of doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md): lane code depends on the trait and receives a concrete instance by injection instead of importing `io.time_ops` or declaring raw `rt_time_now_*`/`rt_sleep_nanos` externs directly. This spec proves the pure test double (`FixedStepClock`) is deterministic -- it starts at zero and only moves when driven, either by `advance()` or by `sleep_until()` -- and that the real adapter (`HostFrameClock`, src/lib/nogc_sync_mut/ui/host_frame_clock.spl) reports a monotonic wall clock.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# FrameClock Port Spec

`FrameClock` is the portable time seam for the WM/GUI/web/2D lane (tranche W1 of doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md): lane code depends on the trait and receives a concrete instance by injection instead of importing `io.time_ops` or declaring raw `rt_time_now_*`/`rt_sleep_nanos` externs directly. This spec proves the pure test double (`FixedStepClock`) is deterministic -- it starts at zero and only moves when driven, either by `advance()` or by `sleep_until()` -- and that the real adapter (`HostFrameClock`, src/lib/nogc_sync_mut/ui/host_frame_clock.spl) reports a monotonic wall clock.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md (W1) |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/ui_frame_clock_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`FrameClock` is the portable time seam for the WM/GUI/web/2D lane (tranche
W1 of doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md): lane code depends on
the trait and receives a concrete instance by injection instead of importing
`io.time_ops` or declaring raw `rt_time_now_*`/`rt_sleep_nanos` externs
directly. This spec proves the pure test double (`FixedStepClock`) is
deterministic -- it starts at zero and only moves when driven, either by
`advance()` or by `sleep_until()` -- and that the real adapter
(`HostFrameClock`, src/lib/nogc_sync_mut/ui/host_frame_clock.spl) reports a
monotonic wall clock.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md (W1)

## Design

**Design:** N/A

## Research

**Research:** N/A

## Examples

`FixedStepClock.new(step_us)` starts at 0. `advance(step_us)` moves the
clock forward by exactly that amount, twice in a row, proving it is not a
constant. `sleep_until(deadline)` jumps forward to the deadline when the
deadline is ahead of "now", and falls back to advancing by `step_us` when
the deadline is not ahead (never goes backwards). `HostFrameClock` is
sampled twice back-to-back and the second reading must not be earlier than
the first.

## Scenarios

### FrameClock -- FixedStepClock (pure test double)

#### starts at time zero

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts at time zero
- A freshly constructed clock has not been driven yet
   - Expected: clock.now_micros() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts at time zero")
step("A freshly constructed clock has not been driven yet")
var clock = FixedStepClock.new(1000)
expect(clock.now_micros()).to_equal(0)
```

</details>

#### advance() moves the clock forward deterministically, not a constant

- advance() moves the clock forward deterministically, not a constant
- Two successive advance() calls each move the clock by step_us
   - Expected: clock.now_micros() equals `500`
   - Expected: clock.now_micros() equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("advance() moves the clock forward deterministically, not a constant")
step("Two successive advance() calls each move the clock by step_us")
var clock = FixedStepClock.new(500)
clock.advance(500)
expect(clock.now_micros()).to_equal(500)
clock.advance(500)
expect(clock.now_micros()).to_equal(1000)
```

</details>

#### sleep_until() jumps forward to a deadline ahead of the current time

- sleep_until() jumps forward to a deadline ahead of the current time
- A deadline ahead of now becomes the new current time exactly
   - Expected: clock.now_micros() equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sleep_until() jumps forward to a deadline ahead of the current time")
step("A deadline ahead of now becomes the new current time exactly")
var clock = FixedStepClock.new(1000)
clock.sleep_until(5000)
expect(clock.now_micros()).to_equal(5000)
```

</details>

#### sleep_until() with a deadline not ahead of now still advances by step_us

- sleep_until() with a deadline not ahead of now still advances by step_us
- A deadline at or behind now never moves the clock backwards
   - Expected: clock.now_micros() equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sleep_until() with a deadline not ahead of now still advances by step_us")
step("A deadline at or behind now never moves the clock backwards")
var clock = FixedStepClock.new(1000)
clock.advance(2000)
clock.sleep_until(500)
expect(clock.now_micros()).to_equal(3000)
```

</details>

### FrameClock -- HostFrameClock (real adapter)

#### now_micros() is monotonic across two back-to-back calls

- now_micros() is monotonic across two back-to-back calls
- Sample the real clock twice; the second reading must not be earlier


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("now_micros() is monotonic across two back-to-back calls")
step("Sample the real clock twice; the second reading must not be earlier")
var clock = HostFrameClock.new()
val t1 = clock.now_micros()
val t2 = clock.now_micros()
assert_true(t2 >= t1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/wm_lane_boundary_ratchet_lanes.md (W1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `663d8595f7765e674317175a1a095783e0a63835b535c120a03eced3177b9c95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `663d8595f7765e674317175a1a095783e0a63835b535c120a03eced3177b9c95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `663d8595f7765e674317175a1a095783e0a63835b535c120a03eced3177b9c95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/ui_frame_clock_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/ui_frame_clock_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/ui_frame_clock_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/ui_frame_clock_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/ui_frame_clock_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/ui_frame_clock_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts at time zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_frame_clock_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advance() moves the clock forward deterministically, not a constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/ui_frame_clock_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sleep_until() jumps forward to a deadline ahead of the current time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
