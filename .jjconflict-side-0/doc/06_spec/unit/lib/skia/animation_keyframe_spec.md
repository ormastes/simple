# Skia Animation Keyframe Specification

> Tests for the keyframe sequencer — mirrors gfx::KeyframeModel and CSS @keyframes. Verifies construction, ordering, and sampling semantics (linear-interpolation at midpoints, clamping at endpoints, empty/duration edge cases).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skia Animation Keyframe Specification

Tests for the keyframe sequencer — mirrors gfx::KeyframeModel and CSS @keyframes. Verifies construction, ordering, and sampling semantics (linear-interpolation at midpoints, clamping at endpoints, empty/duration edge cases).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SKI-ANI-002 |
| Category | Stdlib |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/unit/lib/skia/animation_keyframe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the keyframe sequencer — mirrors gfx::KeyframeModel and CSS
@keyframes. Verifies construction, ordering, and sampling semantics
(linear-interpolation at midpoints, clamping at endpoints, empty/duration
edge cases).

## Scenarios

### animation_keyframe

#### keyframe_sequence_new: empty, count 0, sample returns 0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keyframe_sequence_new: empty, count 0, sample returns 0
   - Expected: count_ok is true
   - Expected: sample_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keyframe_sequence_new: empty, count 0, sample returns 0")
val seq = keyframe_sequence_new(1000.0)
val count = seq.keyframe_count()
val sampled = seq.sample(500.0)
val count_ok = count == 0
val sample_ok = math_abs(sampled - 0.0) < 1e-9
expect(count_ok).to_equal(true)
expect(sample_ok).to_equal(true)
```

</details>

#### add_keyframe: count increments

- add_keyframe: count increments
   - Expected: count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_keyframe: count increments")
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 10.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 20.0, EasingKind.Linear, custom))
val count = seq.keyframe_count()
expect(count).to_equal(2)
```

</details>

#### add_keyframe: sorts by offset (add 0.5, then 0.2, sample agrees with sorted)

- add_keyframe: sorts by offset (add 0.5, then 0.2, sample agrees with sorted)
   - Expected: ok is true
   - Expected: count equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_keyframe: sorts by offset (add 0.5, then 0.2, sample agrees with sorted)")
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 0.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(0.5, 50.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(0.2, 20.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 100.0, EasingKind.Linear, custom))
# After sort, offsets should be 0.0, 0.2, 0.5, 1.0.
# Sample at 0.2 should give exactly 20.0 (the inserted keyframe value).
val sampled = seq.sample(0.2)
val ok = math_abs(sampled - 20.0) < 1e-9
expect(ok).to_equal(true)
val count = seq.keyframe_count()
expect(count).to_equal(4)
```

</details>

#### sample: at offset 0 returns first keyframe value

- sample: at offset 0 returns first keyframe value
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sample: at offset 0 returns first keyframe value")
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 7.5, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 99.0, EasingKind.Linear, custom))
val sampled = seq.sample(0.0)
val ok = math_abs(sampled - 7.5) < 1e-9
expect(ok).to_equal(true)
```

</details>

#### sample: at offset 1 returns last keyframe value

- sample: at offset 1 returns last keyframe value
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sample: at offset 1 returns last keyframe value")
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 7.5, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 99.0, EasingKind.Linear, custom))
val sampled = seq.sample(1.0)
val ok = math_abs(sampled - 99.0) < 1e-9
expect(ok).to_equal(true)
```

</details>

#### sample: at midpoint linearly interpolates when easing is Linear

- sample: at midpoint linearly interpolates when easing is Linear
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sample: at midpoint linearly interpolates when easing is Linear")
val seq = keyframe_sequence_new(1.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 0.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 100.0, EasingKind.Linear, custom))
val sampled = seq.sample(0.5)
val ok = math_abs(sampled - 50.0) < 1e-9
expect(ok).to_equal(true)
expect(sampled).to_be_greater_than(49.0)
expect(sampled).to_be_less_than(51.0)
```

</details>

#### sample: duration 0 clamps to last keyframe

- sample: duration 0 clamps to last keyframe
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sample: duration 0 clamps to last keyframe")
val seq = keyframe_sequence_new(0.0)
val custom = ease_linear()
seq.add_keyframe(keyframe_new(0.0, 0.0, EasingKind.Linear, custom))
seq.add_keyframe(keyframe_new(1.0, 42.0, EasingKind.Linear, custom))
val sampled = seq.sample(0.25)
val ok = math_abs(sampled - 42.0) < 1e-9
expect(ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `0a22dd006b1f97606b06804d5a06a0d259af9fd8d32a4d7af28b9568d2284cd5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0a22dd006b1f97606b06804d5a06a0d259af9fd8d32a4d7af28b9568d2284cd5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0a22dd006b1f97606b06804d5a06a0d259af9fd8d32a4d7af28b9568d2284cd5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/skia/animation_keyframe_spec.spl
mirror: doc/06_spec/unit/lib/skia/animation_keyframe_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/skia/animation_keyframe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/skia/animation_keyframe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/skia/animation_keyframe_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/skia/animation_keyframe_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keyframe_sequence_new: empty, count 0, sample returns 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/animation_keyframe_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add_keyframe: count increments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/skia/animation_keyframe_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add_keyframe: sorts by offset (add 0.5, then 0.2, sample agrees with sorted)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
