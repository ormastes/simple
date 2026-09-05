# Animation Timeline Specification

> Unit oracle for the tick-driven animation timeline: injected elapsed time maps to an eased value between two endpoints. Runs in the unit lane (expectation failures are not masked here) so it is the authoritative gate for the timeline used by the widget Draw-IR pipeline's progress/transition rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Animation Timeline Specification

Unit oracle for the tick-driven animation timeline: injected elapsed time maps to an eased value between two endpoints. Runs in the unit lane (expectation failures are not masked here) so it is the authoritative gate for the timeline used by the widget Draw-IR pipeline's progress/transition rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W1d, G1.6 |
| Category | Stdlib \| Animation |
| Status | Active |
| Source | `test/01_unit/lib/skia/animation_timeline_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit oracle for the tick-driven animation timeline: injected elapsed time maps
to an eased value between two endpoints. Runs in the unit lane (expectation
failures are not masked here) so it is the authoritative gate for the timeline
used by the widget Draw-IR pipeline's progress/transition rendering.

## Scenarios

### animation_timeline

#### linear timeline maps elapsed time directly to value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- linear timeline maps elapsed time directly to value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("linear timeline maps elapsed time directly to value")
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.Linear)
assert_true(math_abs(timeline_value_at(tl, 0.0) - 0.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 25.0) - 25.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 50.0) - 50.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 100.0) - 100.0) < 1e-9)
```

</details>

#### progress clamps to [0,1] and saturates past the duration

- progress clamps to [0,1] and saturates past the duration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("progress clamps to [0,1] and saturates past the duration")
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.Linear)
assert_true(math_abs(timeline_progress(tl, -10.0) - 0.0) < 1e-9)
assert_true(math_abs(timeline_progress(tl, 50.0) - 0.5) < 1e-9)
assert_true(math_abs(timeline_progress(tl, 250.0) - 1.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 250.0) - 100.0) < 1e-9)
```

</details>

#### zero-duration timeline resolves immediately to the end value

- zero-duration timeline resolves immediately to the end value


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero-duration timeline resolves immediately to the end value")
val tl = timeline_new(0.0, 100.0, 0.0, EasingKind.Linear)
assert_true(math_abs(timeline_value_at(tl, 0.0) - 100.0) < 1e-9)
assert_true(timeline_done(tl, 0.0))
```

</details>

#### ease-in-out is symmetric at the midpoint and slow at the ends

- ease-in-out is symmetric at the midpoint and slow at the ends


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ease-in-out is symmetric at the midpoint and slow at the ends")
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.EaseInOut)
val v25 = timeline_value_at(tl, 25.0)
val v40 = timeline_value_at(tl, 40.0)
val v50 = timeline_value_at(tl, 50.0)
val v60 = timeline_value_at(tl, 60.0)
val v75 = timeline_value_at(tl, 75.0)
# midpoint lands at 50 (symmetric curve)
assert_true(math_abs(v50 - 50.0) < 0.5)
# slow start / fast finish: below the diagonal before 50, above after
assert_true(v25 < 25.0)
assert_true(v40 < 40.0)
assert_true(v60 > 60.0)
assert_true(v75 > 75.0)
# the 40ms/60ms samples the widget spec renders land in fill-probe range
assert_true(v40 > 20.0)
assert_true(v60 < 80.0)
```

</details>

#### value is monotonically non-decreasing across ticks

- value is monotonically non-decreasing across ticks


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("value is monotonically non-decreasing across ticks")
val tl = timeline_new(0.0, 100.0, 100.0, EasingKind.EaseInOut)
var prev = timeline_value_at(tl, 0.0)
var t = 10.0
while t <= 100.0:
    val cur = timeline_value_at(tl, t)
    assert_true(cur >= prev - 1e-9)
    prev = cur
    t = t + 10.0
```

</details>

#### endpoints and direction are honored (descending range)

- endpoints and direction are honored (descending range)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("endpoints and direction are honored (descending range)")
val tl = timeline_new(100.0, 0.0, 50.0, EasingKind.Linear)
assert_true(math_abs(timeline_value_at(tl, 0.0) - 100.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 25.0) - 50.0) < 1e-9)
assert_true(math_abs(timeline_value_at(tl, 50.0) - 0.0) < 1e-9)
```

</details>

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

- Canonical SPipe generation for source `c02c8f5fd21da0dd6daa33597b83470768af0c4fb77b646d548b5500d946a148`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c02c8f5fd21da0dd6daa33597b83470768af0c4fb77b646d548b5500d946a148`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c02c8f5fd21da0dd6daa33597b83470768af0c4fb77b646d548b5500d946a148`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/skia/animation_timeline_spec.spl
mirror: doc/06_spec/01_unit/lib/skia/animation_timeline_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/skia/animation_timeline_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/skia/animation_timeline_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/skia/animation_timeline_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'linear timeline maps elapsed time directly to value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/animation_timeline_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'progress clamps to [0,1] and saturates past the duration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/skia/animation_timeline_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'zero-duration timeline resolves immediately to the end value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
