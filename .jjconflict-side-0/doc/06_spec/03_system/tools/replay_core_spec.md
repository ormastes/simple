# Replay Core Specification

> <details>

<!-- sdn-diagram:id=replay_core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_core_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Core Specification

## Scenarios

### ReplayEventKind

#### FunctionEnter to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.FunctionEnter
val v = k.to_i32()
expect(v).to_equal(0)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(0)
```

</details>

#### FunctionExit to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.FunctionExit
val v = k.to_i32()
expect(v).to_equal(1)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(1)
```

</details>

#### Step to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.Step
val v = k.to_i32()
expect(v).to_equal(2)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(2)
```

</details>

#### VariableWrite to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.VariableWrite
val v = k.to_i32()
expect(v).to_equal(3)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(3)
```

</details>

#### BreakpointHit to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.BreakpointHit
val v = k.to_i32()
expect(v).to_equal(4)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(4)
```

</details>

#### Syscall to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.Syscall
val v = k.to_i32()
expect(v).to_equal(5)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(5)
```

</details>

#### Interrupt to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.Interrupt
val v = k.to_i32()
expect(v).to_equal(6)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(6)
```

</details>

#### TimerRead to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.TimerRead
val v = k.to_i32()
expect(v).to_equal(7)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(7)
```

</details>

#### IoRead to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.IoRead
val v = k.to_i32()
expect(v).to_equal(8)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(8)
```

</details>

#### IoWrite to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.IoWrite
val v = k.to_i32()
expect(v).to_equal(9)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(9)
```

</details>

#### CheckpointSave to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.CheckpointSave
val v = k.to_i32()
expect(v).to_equal(10)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(10)
```

</details>

#### CheckpointRestore to_i32 round-trip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ReplayEventKind.CheckpointRestore
val v = k.to_i32()
expect(v).to_equal(11)
expect(ReplayEventKind.from_i32(v).to_i32()).to_equal(11)
```

</details>

### ReplayEvent creation

#### ReplayEvent fields are accessible after construction

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ReplayEvent(
    seq_id: 7,
    kind: ReplayEventKind.Step,
    timestamp: 1000,
    file_hash: 42,
    line: 99,
    name_hash: 0,
    value_a: 10,
    value_b: 20,
)
expect(ev.seq_id).to_equal(7)
expect(ev.kind.to_i32()).to_equal(2)
expect(ev.timestamp).to_equal(1000)
expect(ev.file_hash).to_equal(42)
expect(ev.line).to_equal(99)
expect(ev.value_a).to_equal(10)
expect(ev.value_b).to_equal(20)
```

</details>

### NoopReplayHook

#### is_off returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hook = NoopReplayHook()
expect(hook.is_off()).to_equal(true)
```

</details>

#### is_recording returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hook = NoopReplayHook()
expect(hook.is_recording()).to_equal(false)
```

</details>

#### is_replaying returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hook = NoopReplayHook()
expect(hook.is_replaying()).to_equal(false)
```

</details>

#### timer_read passes value through

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hook = NoopReplayHook()
val result = hook.on_timer_read(1, 42)
expect(result).to_equal(42)
```

</details>

#### io_read passes value through

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hook = NoopReplayHook()
val result = hook.on_io_read(0x1000, 4, 99)
expect(result).to_equal(99)
```

</details>

### ReplayEngine record mode

#### record mode logs events on on_step

1. eng on step
   - Expected: eng.events.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
expect(eng.events.len()).to_equal(0)
eng.on_step("file.spl", 10, 0)
expect(eng.events.len()).to_equal(1)
```

</details>

#### record mode logs events on on_function_enter

1. eng on function enter
   - Expected: eng.events.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
eng.on_function_enter("foo", "mymod")
expect(eng.events.len()).to_equal(1)
```

</details>

#### record mode accumulates multiple events

1. eng on step
2. eng on function enter
3. eng on io write
   - Expected: eng.events.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
eng.on_step("a.spl", 1, 0)
eng.on_function_enter("bar", "mod")
eng.on_io_write(0x10, 4, 255)
expect(eng.events.len()).to_equal(3)
```

</details>

#### record mode is_recording returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
expect(eng.is_recording()).to_equal(true)
```

</details>

#### record mode is_off returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
expect(eng.is_off()).to_equal(false)
```

</details>

#### record mode timer_read logs and returns value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
val v = eng.on_timer_read(0, 77)
expect(v).to_equal(77)
expect(eng.events.len()).to_equal(1)
```

</details>

#### record mode io_read logs and returns value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
val v = eng.on_io_read(0x20, 4, 55)
expect(v).to_equal(55)
expect(eng.events.len()).to_equal(1)
```

</details>

### ReplayEngine off mode

#### off mode is zero cost — no events logged on on_step

1. eng on step
   - Expected: eng.events.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("off")
eng.on_step("file.spl", 1, 0)
expect(eng.events.len()).to_equal(0)
```

</details>

#### off mode is_off returns true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("off")
expect(eng.is_off()).to_equal(true)
```

</details>

#### off mode is_recording returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("off")
expect(eng.is_recording()).to_equal(false)
```

</details>

#### off mode timer_read passes value through

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("off")
val v = eng.on_timer_read(0, 123)
expect(v).to_equal(123)
```

</details>

### ReplayEngine seq_counter

#### seq_counter increments per event

1. eng on step
2. eng on step
   - Expected: eng.events[0].seq_id equals `0`
   - Expected: eng.events[1].seq_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val eng = ReplayEngine.create("record")
eng.on_step("f.spl", 1, 0)
eng.on_step("f.spl", 2, 0)
expect(eng.events[0].seq_id).to_equal(0)
expect(eng.events[1].seq_id).to_equal(1)
```

</details>

### replay_init and replay_get

#### replay_init then replay_get returns non-None engine

1. replay init
   - Expected: is_some is true
2. replay shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_init("record")
val maybe = replay_get()
var is_some = false
if val Some(_) = maybe:
    is_some = true
expect(is_some).to_equal(true)
replay_shutdown()
```

</details>

#### replay_get engine after init is in record mode

1. replay init
2. is recording = eng is recording
   - Expected: is_recording is true
3. replay shutdown


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_init("record")
val maybe = replay_get()
var is_recording = false
if val Some(eng) = maybe:
    is_recording = eng.is_recording()
expect(is_recording).to_equal(true)
replay_shutdown()
```

</details>

### replay_shutdown

#### replay_shutdown clears engine — replay_get returns None

1. replay init
2. replay shutdown
   - Expected: is_none is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
replay_init("record")
replay_shutdown()
val maybe = replay_get()
var is_none = true
if val Some(_) = maybe:
    is_none = false
expect(is_none).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ReplayEventKind
- ReplayEvent creation
- NoopReplayHook
- ReplayEngine record mode
- ReplayEngine off mode
- ReplayEngine seq_counter
- replay_init and replay_get
- replay_shutdown

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
