# Replay Process Rr Specification

> <details>

<!-- sdn-diagram:id=replay_process_rr_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_process_rr_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_process_rr_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_process_rr_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Process Rr Specification

## Scenarios

### ProcessRecorder creation

#### creates with Idle mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rec = ProcessRecorder.create("echo hello", "/tmp/test_trace")
expect(rec.command).to_equal("echo hello")
expect(rec.events.len()).to_equal(0)
expect(rec.next_seq).to_equal(0)
```

</details>

#### on_syscall_enter records entry event

1. var rec = ProcessRecorder create
2. rec on syscall enter
   - Expected: rec.events.len() equals `1`
   - Expected: rec.events[0].payload_a equals `1`
   - Expected: rec.next_seq equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ProcessRecorder.create("cmd", "/tmp/t")
rec.pid = 100
rec.on_syscall_enter(1, [42, 0])
expect(rec.events.len()).to_equal(1)
expect(rec.events[0].payload_a).to_equal(1)
expect(rec.next_seq).to_equal(1)
```

</details>

#### on_syscall_exit records exit event

1. var rec = ProcessRecorder create
2. rec on syscall enter
3. rec on syscall exit
   - Expected: rec.events.len() equals `2`
   - Expected: rec.next_seq equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ProcessRecorder.create("cmd", "/tmp/t")
rec.pid = 100
rec.on_syscall_enter(1, [])
rec.on_syscall_exit(0)
expect(rec.events.len()).to_equal(2)
expect(rec.next_seq).to_equal(2)
```

</details>

#### on_signal records signal event

1. var rec = ProcessRecorder create
2. rec on signal
   - Expected: rec.events.len() equals `1`
   - Expected: kind.to_text() equals `signal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ProcessRecorder.create("cmd", "/tmp/t")
rec.pid = 200
rec.on_signal(9)
expect(rec.events.len()).to_equal(1)
val kind = ProcessEventKind.from_i32(rec.events[0].kind)
expect(kind.to_text()).to_equal("signal")
```

</details>

#### sequence numbers are monotonic across mixed events

1. var rec = ProcessRecorder create
2. rec on syscall enter
3. rec on syscall exit
4. rec on signal
   - Expected: rec.events[0].seq equals `0`
   - Expected: rec.events[1].seq equals `1`
   - Expected: rec.events[2].seq equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rec = ProcessRecorder.create("cmd", "/tmp/t")
rec.pid = 50
rec.on_syscall_enter(1, [])
rec.on_syscall_exit(0)
rec.on_signal(15)
expect(rec.events[0].seq).to_equal(0)
expect(rec.events[1].seq).to_equal(1)
expect(rec.events[2].seq).to_equal(2)
```

</details>

### ProcessReplayer stepping

#### create starts at position 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rpl = ProcessReplayer.create("/tmp/trace")
expect(rpl.position()).to_equal(0)
expect(rpl.event_count()).to_equal(0)
expect(rpl.has_more()).to_equal(false)
```

</details>

#### has_more is true when events exist

1. var rpl = ProcessReplayer create
   - Expected: rpl.has_more() is true
   - Expected: rpl.event_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpl = ProcessReplayer.create("/tmp/trace")
val ev = ProcessReplayEvent.syscall_exit(0, 1, 0, 42)
rpl.events = [ev]
expect(rpl.has_more()).to_equal(true)
expect(rpl.event_count()).to_equal(1)
```

</details>

#### step_forward returns None at end

1. var rpl = ProcessReplayer create
   - Expected: result.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpl = ProcessReplayer.create("/tmp/trace")
val result = rpl.step_forward()
expect(result.is_none()).to_equal(true)
```

</details>

#### step_forward advances cursor and returns result

1. var rpl = ProcessReplayer create
   - Expected: r.event_seq equals `0`
   - Expected: "should have result" equals ``
   - Expected: rpl.position() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpl = ProcessReplayer.create("/tmp/trace")
val ev0 = ProcessReplayEvent.syscall_exit(0, 1, 0, 10)
val ev1 = ProcessReplayEvent.syscall_exit(1, 1, 0, 20)
rpl.events = [ev0, ev1]
val first = rpl.step_forward()
match first:
    case Some(r):
        expect(r.event_seq).to_equal(0)
    case None:
        expect("should have result").to_equal("")
expect(rpl.position()).to_equal(1)
```

</details>

#### current_event returns event without advancing

1. var rpl = ProcessReplayer create
   - Expected: e.payload_a equals `9`
   - Expected: "should have event" equals ``
   - Expected: rpl.position() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpl = ProcessReplayer.create("/tmp/trace")
val ev = ProcessReplayEvent.signal_event(0, 10, 0, 9)
rpl.events = [ev]
val cur = rpl.current_event()
match cur:
    case Some(e):
        expect(e.payload_a).to_equal(9)
    case None:
        expect("should have event").to_equal("")
expect(rpl.position()).to_equal(0)
```

</details>

#### event_at returns event by index

1. var rpl = ProcessReplayer create
   - Expected: e.payload_a equals `20`
   - Expected: "should have event" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var rpl = ProcessReplayer.create("/tmp/trace")
val ev0 = ProcessReplayEvent.syscall_exit(0, 1, 0, 10)
val ev1 = ProcessReplayEvent.syscall_exit(1, 1, 0, 20)
rpl.events = [ev0, ev1]
match rpl.event_at(1):
    case Some(e):
        expect(e.payload_a).to_equal(20)
    case None:
        expect("should have event").to_equal("")
```

</details>

### CheckpointManager

#### starts with zero checkpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
expect(mgr.count()).to_equal(0)
```

</details>

#### create initializes next_id to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
expect(mgr.next_id).to_equal(0)
expect(mgr.checkpoints.len()).to_equal(0)
```

</details>

#### take_checkpoint increments next_id

1. var mgr = CheckpointManager create
   - Expected: cp.checkpoint_id equals `0`
   - Expected: mgr.next_id equals `1`
   - Expected: mgr.count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CheckpointManager.create()
val cp = mgr.take_checkpoint(100)
expect(cp.checkpoint_id).to_equal(0)
expect(mgr.next_id).to_equal(1)
expect(mgr.count()).to_equal(1)
```

</details>

#### find_checkpoint returns None on empty manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
val result = mgr.find_checkpoint(0)
expect(result.is_none()).to_equal(true)
```

</details>

#### nearest_before returns None on empty manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
val result = mgr.nearest_before(100)
expect(result.is_none()).to_equal(true)
```

</details>

#### nearest_before returns closest checkpoint

1. var mgr = CheckpointManager create
2. mgr take checkpoint
3. mgr take checkpoint
4. mgr take checkpoint
   - Expected: cp.event_seq equals `50`
   - Expected: "should find checkpoint" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = CheckpointManager.create()
mgr.take_checkpoint(10)
mgr.take_checkpoint(50)
mgr.take_checkpoint(100)
val result = mgr.nearest_before(60)
match result:
    case Some(cp):
        expect(cp.event_seq).to_equal(50)
    case None:
        expect("should find checkpoint").to_equal("")
```

</details>

#### latest returns None on empty manager

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
val result = mgr.latest()
expect(result.is_none()).to_equal(true)
```

</details>

### DirtyPage and PageCheckpoint

#### DirtyPage.create stores addr and data

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page = DirtyPage.create(4096, [0, 1, 2, 3])
expect(page.addr).to_equal(4096)
expect(page.data.len()).to_equal(4)
```

</details>

#### PageCheckpoint add_register stores value

1. var cp = PageCheckpoint create
2. cp add register
   - Expected: v equals `12345`
   - Expected: "should find register" equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cp = PageCheckpoint.create(0, 100)
cp.add_register("rip", 12345)
match cp.get_register("rip"):
    case Some(v):
        expect(v).to_equal(12345)
    case None:
        expect("should find register").to_equal("")
```

</details>

#### PageCheckpoint get_register returns None for missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = PageCheckpoint.create(0, 0)
val result = cp.get_register("nonexistent")
expect(result.is_none()).to_equal(true)
```

</details>

#### PageCheckpoint.create_for_pid stores pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cp = PageCheckpoint.create_for_pid(1, 500, 9999)
expect(cp.pid).to_equal(9999)
expect(cp.event_seq).to_equal(500)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_process_rr_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ProcessRecorder creation
- ProcessReplayer stepping
- CheckpointManager
- DirtyPage and PageCheckpoint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
