# Replay Kernel Event Specification

> 1. replay set mode

<!-- sdn-diagram:id=replay_kernel_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_kernel_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_kernel_event_spec -> std
replay_kernel_event_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_kernel_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Kernel Event Specification

## Scenarios

### KernelReplayMode

#### default is Off

1. replay set mode
   - Expected: replay_mode().to_i32() equals `KernelReplayMode.Off.to_i32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.Off)
expect(replay_mode().to_i32()).to_equal(KernelReplayMode.Off.to_i32())
```

</details>

#### replay_is_off default true

1. replay set mode
   - Expected: replay_is_off() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.Off)
expect(replay_is_off()).to_equal(true)
```

</details>

#### replay_set_mode to Record — replay_is_recording returns true

1. replay set mode
   - Expected: replay_is_recording() is true
2. replay set mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.Record)
expect(replay_is_recording()).to_equal(true)
replay_set_mode(KernelReplayMode.Off)
```

</details>

#### replay_set_mode to Off — replay_is_off true again

1. replay set mode
2. replay set mode
   - Expected: replay_is_off() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.Record)
replay_set_mode(KernelReplayMode.Off)
expect(replay_is_off()).to_equal(true)
```

</details>

#### replay_is_recording is false when Off

1. replay set mode
   - Expected: replay_is_recording() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.Off)
expect(replay_is_recording()).to_equal(false)
```

</details>

#### ChaosRecord also counts as recording

1. replay set mode
   - Expected: replay_is_recording() is true
2. replay set mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.ChaosRecord)
expect(replay_is_recording()).to_equal(true)
replay_set_mode(KernelReplayMode.Off)
```

</details>

### EventKind to_i32 round-trip

#### Schedule round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = EventKind.Schedule.to_i32()
expect(v).to_equal(0)
expect(EventKind.from_i32(v).to_i32()).to_equal(0)
```

</details>

#### SyscallEnter round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = EventKind.SyscallEnter.to_i32()
expect(v).to_equal(1)
expect(EventKind.from_i32(v).to_i32()).to_equal(1)
```

</details>

#### SyscallExit round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = EventKind.SyscallExit.to_i32()
expect(v).to_equal(2)
expect(EventKind.from_i32(v).to_i32()).to_equal(2)
```

</details>

#### InterruptDeliver round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = EventKind.InterruptDeliver.to_i32()
expect(v).to_equal(3)
expect(EventKind.from_i32(v).to_i32()).to_equal(3)
```

</details>

#### TimerRead round-trips

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = EventKind.TimerRead.to_i32()
expect(v).to_equal(6)
expect(EventKind.from_i32(v).to_i32()).to_equal(6)
```

</details>

### EventKind to_text

#### Schedule to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EventKind.Schedule.to_text()).to_equal("schedule")
```

</details>

#### SyscallEnter to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EventKind.SyscallEnter.to_text()).to_equal("syscall-enter")
```

</details>

#### SyscallExit to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EventKind.SyscallExit.to_text()).to_equal("syscall-exit")
```

</details>

#### InterruptDeliver to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EventKind.InterruptDeliver.to_text()).to_equal("interrupt")
```

</details>

#### TimerRead to_text

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EventKind.TimerRead.to_text()).to_equal("timer-read")
```

</details>

### ReplayEntry creation

#### create sets kind field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.SyscallEnter, 42, 1, 0)
expect(entry.kind).to_equal(EventKind.SyscallEnter.to_i32())
```

</details>

#### create sets thread_id field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.Schedule, 99, 2, 0)
expect(entry.thread_id).to_equal(99)
```

</details>

#### create sets process_id field

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.Schedule, 1, 77, 0)
expect(entry.process_id).to_equal(77)
```

</details>

#### create sets event_id to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
expect(entry.event_id).to_equal(0)
```

</details>

#### event_kind() returns correct kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = ReplayEntry.create(EventKind.SyscallExit, 1, 1, 0)
expect(entry.event_kind()).to_equal(EventKind.SyscallExit)
```

</details>

### replay ring buffer

#### replay_buffer_init — event_count is 0

1. replay set mode
2. replay buffer reset
3. replay buffer init
   - Expected: replay_event_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.Off)
replay_buffer_reset()
replay_buffer_init()
expect(replay_event_count()).to_equal(0)
```

</details>

#### replay_log_event — event_count becomes 1

1. replay buffer reset
2. replay set mode
3. replay log event
   - Expected: replay_event_count() equals `1`
4. replay set mode
5. replay buffer reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_buffer_reset()
replay_set_mode(KernelReplayMode.Record)
val entry = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
replay_log_event(entry)
expect(replay_event_count()).to_equal(1)
replay_set_mode(KernelReplayMode.Off)
replay_buffer_reset()
```

</details>

#### replay_log_event multiple — count matches

1. replay buffer reset
2. replay set mode
3. replay log event
4. replay log event
5. replay log event
6. replay log event
7. replay log event
   - Expected: replay_event_count() equals `5`
8. replay set mode
9. replay buffer reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_buffer_reset()
replay_set_mode(KernelReplayMode.Record)
val e0 = ReplayEntry.create(EventKind.Schedule, 0, 1, 0)
val e1 = ReplayEntry.create(EventKind.Schedule, 1, 1, 0)
val e2 = ReplayEntry.create(EventKind.Schedule, 2, 1, 0)
val e3 = ReplayEntry.create(EventKind.Schedule, 3, 1, 0)
val e4 = ReplayEntry.create(EventKind.Schedule, 4, 1, 0)
replay_log_event(e0)
replay_log_event(e1)
replay_log_event(e2)
replay_log_event(e3)
replay_log_event(e4)
expect(replay_event_count()).to_equal(5)
replay_set_mode(KernelReplayMode.Off)
replay_buffer_reset()
```

</details>

#### replay_buffer_reset — count returns to 0

1. replay set mode
2. replay log event
3. replay buffer reset
   - Expected: replay_event_count() equals `0`
4. replay set mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_set_mode(KernelReplayMode.Record)
val entry = ReplayEntry.create(EventKind.TimerRead, 1, 1, 0)
replay_log_event(entry)
replay_buffer_reset()
expect(replay_event_count()).to_equal(0)
replay_set_mode(KernelReplayMode.Off)
```

</details>

#### replay_read_next — returns logged entry fields

1. replay buffer reset
2. replay set mode
3. var entry = ReplayEntry create
4. replay log event
5. replay set mode
   - Expected: got.kind equals `EventKind.SyscallEnter.to_i32()`
   - Expected: got.thread_id equals `55`
   - Expected: got.payload_a equals `123`
   - Expected: "read_next returned None" equals `expected Some`
6. replay set mode
7. replay buffer reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_buffer_reset()
replay_set_mode(KernelReplayMode.Record)
var entry = ReplayEntry.create(EventKind.SyscallEnter, 55, 7, 2)
entry.payload_a = 123
replay_log_event(entry)
replay_set_mode(KernelReplayMode.Replay)
match replay_read_next():
    case Some(got):
        expect(got.kind).to_equal(EventKind.SyscallEnter.to_i32())
        expect(got.thread_id).to_equal(55)
        expect(got.payload_a).to_equal(123)
    case None:
        expect("read_next returned None").to_equal("expected Some")
replay_set_mode(KernelReplayMode.Off)
replay_buffer_reset()
```

</details>

#### replay_read_next on empty buffer returns None

1. replay buffer reset
2. replay set mode
   - Expected: "expected None but got Some" equals `None`
   - Expected: replay_mode().to_i32() equals `KernelReplayMode.Replay.to_i32()`
3. replay set mode
4. replay buffer reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_buffer_reset()
replay_set_mode(KernelReplayMode.Replay)
match replay_read_next():
    case Some(_):
        expect("expected None but got Some").to_equal("None")
    case None:
        expect(replay_mode().to_i32()).to_equal(KernelReplayMode.Replay.to_i32())
replay_set_mode(KernelReplayMode.Off)
replay_buffer_reset()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_kernel_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- KernelReplayMode
- EventKind to_i32 round-trip
- EventKind to_text
- ReplayEntry creation
- replay ring buffer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
