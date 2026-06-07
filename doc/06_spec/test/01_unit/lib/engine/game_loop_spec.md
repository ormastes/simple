# game_loop_spec

> Engine Game Loop — GameLoop state machine tests

<!-- sdn-diagram:id=game_loop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game_loop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game_loop_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game_loop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# game_loop_spec

Engine Game Loop — GameLoop state machine tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/game_loop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Game Loop — GameLoop state machine tests

Tests GameLoop creation, initial state, stop, pause/unpause toggle.
Does not call run() to avoid requiring a full Engine2D and window.

## Scenarios

### GameLoop

#### create sets running false and paused false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gl = GameLoop.create(Seconds(value: 0.016666))
expect(gl.running).to_equal(false)
expect(gl.paused).to_equal(false)
```

</details>

#### is_running returns false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gl = GameLoop.create(Seconds(value: 0.016666))
expect(gl.is_running()).to_equal(false)
```

</details>

#### is_paused returns false initially

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gl = GameLoop.create(Seconds(value: 0.016666))
expect(gl.is_paused()).to_equal(false)
```

</details>

#### stop sets running to false

1. var gl = GameLoop create
   - Expected: gl.is_running() is true
2. gl stop
   - Expected: gl.is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gl = GameLoop.create(Seconds(value: 0.016666))
# Manually set running to true to test stop()
gl.running = true
expect(gl.is_running()).to_equal(true)
gl.stop()
expect(gl.is_running()).to_equal(false)
```

</details>

#### pause sets paused to true

1. var gl = GameLoop create
2. gl pause
   - Expected: gl.is_paused() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gl = GameLoop.create(Seconds(value: 0.016666))
gl.pause()
expect(gl.is_paused()).to_equal(true)
```

</details>

#### unpause sets paused to false

1. var gl = GameLoop create
2. gl pause
   - Expected: gl.is_paused() is true
3. gl unpause
   - Expected: gl.is_paused() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gl = GameLoop.create(Seconds(value: 0.016666))
gl.pause()
expect(gl.is_paused()).to_equal(true)
gl.unpause()
expect(gl.is_paused()).to_equal(false)
```

</details>

#### pause and unpause toggle paused state

1. var gl = GameLoop create
   - Expected: gl.is_paused() is false
2. gl pause
   - Expected: gl.is_paused() is true
3. gl unpause
   - Expected: gl.is_paused() is false
4. gl pause
   - Expected: gl.is_paused() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var gl = GameLoop.create(Seconds(value: 0.016666))
expect(gl.is_paused()).to_equal(false)
gl.pause()
expect(gl.is_paused()).to_equal(true)
gl.unpause()
expect(gl.is_paused()).to_equal(false)
gl.pause()
expect(gl.is_paused()).to_equal(true)
```

</details>

### Clock

#### create starts with zero accumulator and frame count

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val clock = Clock.create(Seconds(value: 0.016666))
val acc_i = clock.get_accumulator() * 1000.0
expect(acc_i).to_be_greater_than(-1.0)
expect(acc_i).to_be_less_than(1.0)
expect(clock.frame_count).to_equal(0)
```

</details>

#### tick computes delta from nanoseconds

1. var clock = Clock create
   - Expected: frame1.frame_count equals `1`
   - Expected: frame2.frame_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var clock = Clock.create(Seconds(value: 0.016666))
# First tick initializes last_time_ns, delta = 0
val frame1 = clock.tick(1000000000)
val d1_i = frame1.delta.value * 1000.0
expect(d1_i).to_be_greater_than(-1.0)
expect(d1_i).to_be_less_than(1.0)
expect(frame1.frame_count).to_equal(1)
# Second tick: 16ms later
val frame2 = clock.tick(1016000000)
val d2_i = frame2.delta.value * 1000.0
# Should be about 16ms = 0.016
expect(d2_i).to_be_greater_than(15.0)
expect(d2_i).to_be_less_than(17.0)
expect(frame2.frame_count).to_equal(2)
```

</details>

#### consume_fixed_steps drains accumulator

1. var clock = Clock create


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var clock = Clock.create(Seconds(value: 0.016666))
# First tick (init)
val f1 = clock.tick(1000000000)
# Second tick: 50ms later (should yield ~3 physics steps at 16.666ms each)
val f2 = clock.tick(1050000000)
val steps = clock.consume_fixed_steps()
expect(steps).to_be_greater_than(0)
```

</details>

#### get_interpolation_alpha returns value in 0 to 1 range

1. var clock = Clock create


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var clock = Clock.create(Seconds(value: 0.016666))
val f1 = clock.tick(1000000000)
val f2 = clock.tick(1010000000)
val steps = clock.consume_fixed_steps()
val alpha = clock.get_interpolation_alpha()
val alpha_i = alpha * 1000.0
expect(alpha_i).to_be_greater_than(-1.0)
expect(alpha_i).to_be_less_than(1001.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
