# Game2D Event Replay & Animation (capture-backed)

> Runtime (non-grep) capture spec for the game2d event/animation stack. Drives real `App` implementations through `LoopDriver.run_frames` against a `HeadlessBackend` software framebuffer with `ScriptedInput` snapshot lists:

<!-- sdn-diagram:id=game2d_event_replay_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_event_replay_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_event_replay_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_event_replay_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

- ScriptedInput new
- ScriptedInput new
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = replay_blink(
    ScriptedInput.new([empty_snap(), empty_snap(), empty_snap()]))
val pressed = replay_blink(
    ScriptedInput.new([empty_snap(), press_snap(), empty_snap()]))
assert_not_equal(base, pressed)
```

</details>

#### identical replays are byte-equal (determinism)

- ScriptedInput new
- ScriptedInput new
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_a = replay_blink(
    ScriptedInput.new([empty_snap(), press_snap(), empty_snap()]))
val run_b = replay_blink(
    ScriptedInput.new([empty_snap(), press_snap(), empty_snap()]))
assert_equal(run_a, run_b)
```

</details>

#### no-input replay is also deterministic and distinct from pressed

- assert equal
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val quiet_a = replay_blink(ScriptedInput.new([empty_snap()]))
val quiet_b = replay_blink(ScriptedInput.new([empty_snap()]))
val pressed = replay_blink(ScriptedInput.new([press_snap()]))
assert_equal(quiet_a, quiet_b)
assert_not_equal(quiet_a, pressed)
```

</details>

### Game2D Animation Capture (W8/G1.6)

#### rect animation: no two consecutive frame hashes are equal

- assert equal
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hashes = sample_slide_hashes(6)
assert_equal(hashes.len(), 6)
var i: i64 = 1
while i < 6:
    assert_not_equal(hashes[i as i32], hashes[(i - 1) as i32])
    i = i + 1
```

</details>

#### animation replay is deterministic frame-by-frame

- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W8)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W8))
- **Design:** [src/lib/nogc_sync_mut/game2d/loop/driver.spl (`run_frames`)](src/lib/nogc_sync_mut/game2d/loop/driver.spl (`run_frames`))


</details>
