# animation_fsm_spec

> Animation FSM — state machine animation tests

<!-- sdn-diagram:id=animation_fsm_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=animation_fsm_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

animation_fsm_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=animation_fsm_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# animation_fsm_spec

Animation FSM — state machine animation tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/animation_fsm_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Animation FSM — state machine animation tests

Tests AnimClip creation, AnimState lifecycle, AnimationFSM state management,
transition triggering, update advancement, auto-transitions, and blending.

## Scenarios

### AnimClip

#### creates with correct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clip = AnimClip.new("walk", 8, 0.1, true)
expect(clip.name).to_equal("walk")
expect(clip.frame_count).to_equal(8)
expect(clip.looping).to_equal(true)
```

</details>

#### total_duration returns frame_count * frame_duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clip = AnimClip.new("run", 10, 0.05, false)
val dur = clip.total_duration()
# 10 * 0.05 = 0.5
val dur_i = dur * 1000.0
expect(dur_i).to_be_greater_than(499.0)
expect(dur_i).to_be_less_than(501.0)
```

</details>

### AnimState

#### creates with zero elapsed and frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clip = AnimClip.new("idle", 4, 0.25, true)
val s = AnimState.new("idle", clip)
expect(s.name).to_equal("idle")
expect(s.elapsed).to_equal(0.0)
expect(s.current_frame).to_equal(0)
```

</details>

<details>
<summary>Advanced: is_finished false when looping</summary>

#### is_finished false when looping

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clip = AnimClip.new("idle", 4, 0.25, true)
val s = AnimState(name: "idle", clip: clip, elapsed: 10.0, current_frame: 3)
expect(s.is_finished()).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: is_finished true when non-looping and elapsed past duration</summary>

#### is_finished true when non-looping and elapsed past duration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val clip = AnimClip.new("attack", 4, 0.25, false)
val s = AnimState(name: "attack", clip: clip, elapsed: 2.0, current_frame: 3)
expect(s.is_finished()).to_equal(true)
```

</details>


</details>

### AnimationFSM

#### starts empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fsm = AnimationFSM.new()
expect(fsm.state_count()).to_equal(0)
expect(fsm.is_transitioning()).to_equal(false)
```

</details>

#### add_state increases state count

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm add state
   - Expected: fsm.state_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.add_state("run", AnimClip.new("run", 8, 0.1, true))
expect(fsm.state_count()).to_equal(2)
```

</details>

#### set_initial sets current state name

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm set initial
   - Expected: fsm.get_current_state_name() equals `idle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.set_initial("idle")
expect(fsm.get_current_state_name()).to_equal("idle")
```

</details>

#### trigger_transition returns false with no matching rule

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm add state
4. fsm set initial
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.add_state("run", AnimClip.new("run", 8, 0.1, true))
fsm.set_initial("idle")
val ok = fsm.trigger_transition("run")
expect(ok).to_equal(false)
```

</details>

#### trigger_transition returns true with matching rule

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm add state
4. fsm add transition
5. fsm set initial
   - Expected: ok is true
   - Expected: fsm.is_transitioning() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.add_state("run", AnimClip.new("run", 8, 0.1, true))
fsm.add_transition("idle", "run", 0.3, false)
fsm.set_initial("idle")
val ok = fsm.trigger_transition("run")
expect(ok).to_equal(true)
expect(fsm.is_transitioning()).to_equal(true)
```

</details>

#### update advances frame

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm set initial
4. fsm update
   - Expected: frame equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.set_initial("idle")
fsm.update(0.3)
val frame = fsm.get_current_frame()
# 0.3 / 0.25 = 1.2 -> frame 1
expect(frame).to_equal(1)
```

</details>

#### update completes transition

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm add state
4. fsm add transition
5. fsm set initial
6. fsm trigger transition
7. fsm update
   - Expected: fsm.is_transitioning() is false
   - Expected: fsm.get_current_state_name() equals `run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.add_state("run", AnimClip.new("run", 8, 0.1, true))
fsm.add_transition("idle", "run", 0.2, false)
fsm.set_initial("idle")
fsm.trigger_transition("run")
# Advance past transition duration
fsm.update(0.3)
expect(fsm.is_transitioning()).to_equal(false)
expect(fsm.get_current_state_name()).to_equal("run")
```

</details>

#### blend_alpha progresses during transition

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm add state
4. fsm add transition
5. fsm set initial
6. fsm trigger transition
7. fsm update


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.add_state("run", AnimClip.new("run", 8, 0.1, true))
fsm.add_transition("idle", "run", 1.0, false)
fsm.set_initial("idle")
fsm.trigger_transition("run")
fsm.update(0.5)
# blend_alpha should be ~0.5
val alpha = fsm.get_blend_alpha()
val alpha_i = alpha * 1000.0
expect(alpha_i).to_be_greater_than(490.0)
expect(alpha_i).to_be_less_than(510.0)
```

</details>

#### auto-transition triggers when clip finishes

1. var fsm = AnimationFSM new
2. fsm add state
3. fsm add state
4. fsm add transition
5. fsm set initial
6. fsm update
   - Expected: fsm.is_transitioning() is true
   - Expected: fsm.get_current_state_name() equals `attack`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fsm = AnimationFSM.new()
# attack: 4 frames * 0.1s = 0.4s total, non-looping
fsm.add_state("attack", AnimClip.new("attack", 4, 0.1, false))
fsm.add_state("idle", AnimClip.new("idle", 4, 0.25, true))
fsm.add_transition("attack", "idle", 0.2, true)
fsm.set_initial("attack")
# Advance past attack duration
fsm.update(0.5)
expect(fsm.is_transitioning()).to_equal(true)
expect(fsm.get_current_state_name()).to_equal("attack")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
