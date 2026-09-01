# Game2D Event Replay & Animation (capture-backed)

> Runtime (non-grep) capture spec for the game2d event/animation stack. Drives real `App` implementations through `LoopDriver.run_frames` against a `HeadlessBackend` software framebuffer with `ScriptedInput` snapshot lists:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2D Event Replay & Animation (capture-backed)

Runtime (non-grep) capture spec for the game2d event/animation stack. Drives real `App` implementations through `LoopDriver.run_frames` against a `HeadlessBackend` software framebuffer with `ScriptedInput` snapshot lists:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W8, G1.5, G1.6 |
| Category | Testing \| Runtime \| GUI |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W8) |
| Design | src/lib/nogc_sync_mut/game2d/loop/driver.spl (`run_frames`) |
| Source | `test/03_system/game2d/game2d_event_replay_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runtime (non-grep) capture spec for the game2d event/animation stack. Drives
real `App` implementations through `LoopDriver.run_frames` against a
`HeadlessBackend` software framebuffer with `ScriptedInput` snapshot lists:

1. **Event replay** — a scripted key press flips app state; the final
   `frame_hash` must differ from an identical replay without the press.
2. **Determinism** — the same scripted replay run twice produces byte-equal
   framebuffers (identical hashes).
3. **Animation** — an app that moves a rect one step per `fixed_update`;
   frame hashes sampled after each pumped frame must all differ from their
   predecessor (the rect visibly moved every fixed step).

Framebuffer is tiny (64x48) and frame counts small so the interpreter-mode
runner stays fast.

## Related Specifications

- [game2d_golden_spec.spl](../../system/game2d_golden_spec.spl) — golden hash pin
- [game2d_replay_spec.spl](../../system/game2d_replay_spec.spl) — replay contract (grep-level)

## Scenarios

### Game2D Event Replay (W8/G1.5)

#### scripted key press changes the captured frame hash

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scripted key press changes the captured frame hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scripted key press changes the captured frame hash")
val base = replay_blink(
    ScriptedInput.new([empty_snap(), empty_snap(), empty_snap()]))
val pressed = replay_blink(
    ScriptedInput.new([empty_snap(), press_snap(), empty_snap()]))
assert_not_equal(base, pressed)
```

</details>

#### identical replays are byte-equal (determinism)

- identical replays are byte-equal (determinism)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identical replays are byte-equal (determinism)")
val run_a = replay_blink(
    ScriptedInput.new([empty_snap(), press_snap(), empty_snap()]))
val run_b = replay_blink(
    ScriptedInput.new([empty_snap(), press_snap(), empty_snap()]))
assert_equal(run_a, run_b)
```

</details>

#### no-input replay is also deterministic and distinct from pressed

- no-input replay is also deterministic and distinct from pressed


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no-input replay is also deterministic and distinct from pressed")
val quiet_a = replay_blink(ScriptedInput.new([empty_snap()]))
val quiet_b = replay_blink(ScriptedInput.new([empty_snap()]))
val pressed = replay_blink(ScriptedInput.new([press_snap()]))
assert_equal(quiet_a, quiet_b)
assert_not_equal(quiet_a, pressed)
```

</details>

### Game2D Animation Capture (W8/G1.6)

#### rect animation: no two consecutive frame hashes are equal

- rect animation: no two consecutive frame hashes are equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rect animation: no two consecutive frame hashes are equal")
val hashes = sample_slide_hashes(6)
assert_equal(hashes.len(), 6)
var i: i64 = 1
while i < 6:
    assert_not_equal(hashes[i as i32], hashes[(i - 1) as i32])
    i = i + 1
```

</details>

#### animation replay is deterministic frame-by-frame

- animation replay is deterministic frame-by-frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("animation replay is deterministic frame-by-frame")
val a = sample_slide_hashes(4)
val b = sample_slide_hashes(4)
var i: i64 = 0
while i < 4:
    assert_equal(a[i as i32], b[i as i32])
    i = i + 1
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

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W8)`
- **Design:** `src/lib/nogc_sync_mut/game2d/loop/driver.spl (`run_frames`)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8f6039a15b87f184b8ed9f2079ba3746ec6eccde66768be7a77ccb157b08a347`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f6039a15b87f184b8ed9f2079ba3746ec6eccde66768be7a77ccb157b08a347`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f6039a15b87f184b8ed9f2079ba3746ec6eccde66768be7a77ccb157b08a347`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/game2d/game2d_event_replay_spec.spl
mirror: doc/06_spec/03_system/game2d/game2d_event_replay_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/game2d/game2d_event_replay_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/game2d/game2d_event_replay_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/game2d/game2d_event_replay_spec.spl:165:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scripted key press changes the captured frame hash' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/game2d/game2d_event_replay_spec.spl:174:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical replays are byte-equal (determinism)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/game2d/game2d_event_replay_spec.spl:183:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no-input replay is also deterministic and distinct from pressed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
