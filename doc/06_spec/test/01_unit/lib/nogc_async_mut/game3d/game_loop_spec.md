# Game Loop Specification

> 1. set init callback

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
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game Loop Specification

## Scenarios

### GameLoop callback registration

#### when registering init callback

#### calls init callback and returns its return value

1. set init callback
   - Expected: result equals `42`
   - Expected: init_called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
init_called = false
set_init_callback(test_init)
val result = game_init()
expect(result).to_equal(42)
expect(init_called).to_equal(true)
```

</details>

#### when registering update callback

#### calls update callback with delta time

1. set update callback
2. game update
   - Expected: update_called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
update_called = false
last_dt = 0.0
set_update_callback(test_update)
game_update(0.016)
expect(update_called).to_equal(true)
```

</details>

#### when registering shutdown callback

#### calls shutdown callback

1. set shutdown callback
2. game shutdown
   - Expected: shutdown_called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shutdown_called = false
set_shutdown_callback(test_shutdown)
game_shutdown()
expect(shutdown_called).to_equal(true)
```

</details>

#### when registering fixed update callback

#### calls fixed update callback with delta time

1. set fixed update callback
2. game fixed update
   - Expected: fixed_update_called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fixed_update_called = false
last_dt = 0.0
set_fixed_update_callback(test_fixed_update)
game_fixed_update(0.02)
expect(fixed_update_called).to_equal(true)
```

</details>

#### when registering input callback

#### calls input callback with event type, key, and value

1. set input callback
2. on input event
   - Expected: input_called is true
   - Expected: last_input_type equals `1`
   - Expected: last_input_key equals `65`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
input_called = false
last_input_type = 0
last_input_key = 0
last_input_value = 0.0
set_input_callback(test_input)
on_input_event(1, 65, 1.0)
expect(input_called).to_equal(true)
expect(last_input_type).to_equal(1)
expect(last_input_key).to_equal(65)
```

</details>

### GameLoop event queue

#### get_event_queue

#### returns the shared event queue

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
expect(q.?).to_equal(true)
```

</details>

#### on_collision

#### pushes a collision event into the queue

1. q clear
2. on collision
   - Expected: q.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
q.clear()
on_collision(1, 2, 0.0, 1.0, 0.0)
expect(q.count()).to_equal(1)
```

</details>

#### stores correct entity ids in collision event

1. q clear
2. on collision
   - Expected: ev.entity_a equals `10`
   - Expected: ev.entity_b equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
q.clear()
on_collision(10, 20, 0.5, 0.5, 0.5)
val ev = q.get(0)
expect(ev.entity_a).to_equal(10)
expect(ev.entity_b).to_equal(20)
```

</details>

#### stores correct normal in collision event

1. q clear
2. on collision
   - Expected: ev.event_type.to_i32() equals `GameEventType.CollisionEnter.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
q.clear()
on_collision(1, 2, 1.0, 0.0, 0.0)
val ev = q.get(0)
expect(ev.event_type.to_i32()).to_equal(GameEventType.CollisionEnter.to_i32())
```

</details>

#### on_trigger

#### pushes a trigger-enter event when entered is non-zero

1. q clear
2. on trigger
   - Expected: q.count() equals `1`
   - Expected: ev.event_type.to_i32() equals `GameEventType.TriggerEnter.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
q.clear()
on_trigger(3, 4, 1)
expect(q.count()).to_equal(1)
val ev = q.get(0)
expect(ev.event_type.to_i32()).to_equal(GameEventType.TriggerEnter.to_i32())
```

</details>

#### pushes a trigger-exit event when entered is zero

1. q clear
2. on trigger
   - Expected: q.count() equals `1`
   - Expected: ev.event_type.to_i32() equals `GameEventType.TriggerExit.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
q.clear()
on_trigger(5, 6, 0)
expect(q.count()).to_equal(1)
val ev = q.get(0)
expect(ev.event_type.to_i32()).to_equal(GameEventType.TriggerExit.to_i32())
```

</details>

#### stores correct entity ids in trigger event

1. q clear
2. on trigger
   - Expected: ev.entity_a equals `7`
   - Expected: ev.entity_b equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
q.clear()
on_trigger(7, 8, 1)
val ev = q.get(0)
expect(ev.entity_a).to_equal(7)
expect(ev.entity_b).to_equal(8)
```

</details>

#### game_update clears events

#### empties the event queue on each game_update call

1. on collision
2. on trigger
3. set update callback
4. game update
   - Expected: q.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
on_collision(1, 2, 0.0, 0.0, 1.0)
on_trigger(3, 4, 1)
set_update_callback(test_update)
game_update(0.016)
expect(q.count()).to_equal(0)
```

</details>

#### accumulates new events after game_update clears

1. set update callback
2. game update
3. on collision
   - Expected: q.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = get_event_queue()
set_update_callback(test_update)
game_update(0.016)
on_collision(9, 10, 0.0, 1.0, 0.0)
expect(q.count()).to_equal(1)
```

</details>

### GameLoop export functions

#### game_init

#### passes delta time through to update callback

1. set update callback
2. game update
   - Expected: update_called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
update_called = false
last_dt = 0.0
set_update_callback(test_update)
game_update(0.033)
expect(update_called).to_equal(true)
```

</details>

#### game_fixed_update

#### calls registered fixed update callback

1. set fixed update callback
2. game fixed update
   - Expected: fixed_update_called is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fixed_update_called = false
set_fixed_update_callback(test_fixed_update)
game_fixed_update(0.02)
expect(fixed_update_called).to_equal(true)
```

</details>

#### on_input_event

#### forwards all three input parameters to the callback

1. set input callback
2. on input event
   - Expected: input_called is true
   - Expected: last_input_type equals `2`
   - Expected: last_input_key equals `87`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
input_called = false
last_input_type = 0
last_input_key = 0
last_input_value = 0.0
set_input_callback(test_input)
on_input_event(2, 87, 0.75)
expect(input_called).to_equal(true)
expect(last_input_type).to_equal(2)
expect(last_input_key).to_equal(87)
```

</details>

### GameLoop default behavior with no callbacks

#### game_init with nil callback

#### returns 0 when no init callback is registered

1. set init callback
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_init_callback(nil)
val result = game_init()
expect(result).to_equal(0)
```

</details>

#### game_update with nil callback

#### does not crash when no update callback is registered

1. on collision
2. set update callback
3. game update
   - Expected: update_called is false
   - Expected: last_dt equals `0.0`
   - Expected: q.count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
update_called = false
last_dt = 0.0
val q = get_event_queue()
on_collision(21, 22, 0.0, 0.0, 1.0)
set_update_callback(nil)
game_update(0.016)
expect(update_called).to_equal(false)
expect(last_dt).to_equal(0.0)
expect(q.count()).to_equal(0)
```

</details>

#### game_shutdown with nil callback

#### does not crash when no shutdown callback is registered

1. set shutdown callback
2. game shutdown
   - Expected: shutdown_called is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shutdown_called = false
set_shutdown_callback(nil)
game_shutdown()
expect(shutdown_called).to_equal(false)
```

</details>

#### game_fixed_update with nil callback

#### does not crash when no fixed update callback is registered

1. set fixed update callback
2. game fixed update
   - Expected: fixed_update_called is false
   - Expected: last_dt equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fixed_update_called = false
last_dt = 0.0
set_fixed_update_callback(nil)
game_fixed_update(0.02)
expect(fixed_update_called).to_equal(false)
expect(last_dt).to_equal(0.0)
```

</details>

#### on_input_event with nil callback

#### does not crash when no input callback is registered

1. set input callback
2. on input event
   - Expected: input_called is false
   - Expected: last_input_type equals `123`
   - Expected: last_input_key equals `456`
   - Expected: last_input_value equals `7.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
input_called = false
last_input_type = 123
last_input_key = 456
last_input_value = 7.5
set_input_callback(nil)
on_input_event(0, 0, 0.0)
expect(input_called).to_equal(false)
expect(last_input_type).to_equal(123)
expect(last_input_key).to_equal(456)
expect(last_input_value).to_equal(7.5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/game_loop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- GameLoop callback registration
- GameLoop event queue
- GameLoop export functions
- GameLoop default behavior with no callbacks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
