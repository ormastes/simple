# Replay Process E2e Specification

> <details>

<!-- sdn-diagram:id=replay_process_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_process_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_process_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_process_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Process E2e Specification

## Scenarios

### ProcessRecorder initial state

#### events list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessRecorder.create("echo hello", "/tmp/traces")
expect(r.events.len()).to_equal(0)
```

</details>

#### next_seq starts at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessRecorder.create("echo hello", "/tmp/traces")
expect(r.next_seq).to_equal(0)
```

</details>

#### pid starts at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessRecorder.create("echo hello", "/tmp/traces")
expect(r.pid).to_equal(0)
```

</details>

#### strace_path is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessRecorder.create("echo hello", "/tmp/traces")
expect(r.strace_path).to_equal("")
```

</details>

#### pending_syscall_id is -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessRecorder.create("echo hello", "/tmp/traces")
expect(r.pending_syscall_id).to_equal(-1)
```

</details>

#### command field is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessRecorder.create("echo hello", "/tmp/traces")
expect(r.command).to_equal("echo hello")
```

</details>

#### trace_dir field is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessRecorder.create("echo hello", "/tmp/traces")
expect(r.trace_dir).to_equal("/tmp/traces")
```

</details>

### ProcessEventKind variants

#### SyscallEntry to_i32 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.SyscallEntry.to_i32()).to_equal(0)
```

</details>

#### SyscallExit to_i32 is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.SyscallExit.to_i32()).to_equal(1)
```

</details>

#### Signal to_i32 is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.Signal.to_i32()).to_equal(2)
```

</details>

#### MmapResult to_i32 is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.MmapResult.to_i32()).to_equal(3)
```

</details>

#### TimeQuery to_i32 is 4

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.TimeQuery.to_i32()).to_equal(4)
```

</details>

#### RandomBytes to_i32 is 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.RandomBytes.to_i32()).to_equal(5)
```

</details>

#### Checkpoint to_i32 is 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.Checkpoint.to_i32()).to_equal(6)
```

</details>

#### ThreadSwitch to_i32 is 7

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.ThreadSwitch.to_i32()).to_equal(7)
```

</details>

#### ProcessCreate to_i32 is 8

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.ProcessCreate.to_i32()).to_equal(8)
```

</details>

#### ProcessExit to_i32 is 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ProcessEventKind.ProcessExit.to_i32()).to_equal(9)
```

</details>

#### from_i32 round-trips SyscallEntry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ProcessEventKind.from_i32(0)
expect(v.to_i32()).to_equal(0)
```

</details>

#### from_i32 round-trips SyscallExit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ProcessEventKind.from_i32(1)
expect(v.to_i32()).to_equal(1)
```

</details>

#### from_i32 round-trips Signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ProcessEventKind.from_i32(2)
expect(v.to_i32()).to_equal(2)
```

</details>

#### from_i32 round-trips ProcessExit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ProcessEventKind.from_i32(9)
expect(v.to_i32()).to_equal(9)
```

</details>

#### from_i32 unknown falls back to SyscallEntry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ProcessEventKind.from_i32(99)
expect(v.to_i32()).to_equal(0)
```

</details>

### ProcessReplayEvent constructors

#### syscall_entry sets kind to SyscallEntry

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(1, 100, 999, 60, 0, 0)
expect(ev.kind).to_equal(ProcessEventKind.SyscallEntry.to_i32())
```

</details>

#### syscall_entry stores seq

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(7, 100, 999, 60, 0, 0)
expect(ev.seq).to_equal(7)
```

</details>

#### syscall_entry stores tid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(1, 42, 999, 60, 0, 0)
expect(ev.tid).to_equal(42)
```

</details>

#### syscall_entry stores syscall_nr in payload_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(1, 100, 999, 60, 3, 4)
expect(ev.payload_a).to_equal(60)
```

</details>

#### syscall_exit sets kind to SyscallExit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_exit(2, 100, 999, 0)
expect(ev.kind).to_equal(ProcessEventKind.SyscallExit.to_i32())
```

</details>

#### syscall_exit stores retval in payload_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_exit(2, 100, 999, 42)
expect(ev.payload_a).to_equal(42)
```

</details>

#### signal_event sets kind to Signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.signal_event(3, 100, 999, 11)
expect(ev.kind).to_equal(ProcessEventKind.Signal.to_i32())
```

</details>

#### signal_event stores signum in payload_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.signal_event(3, 100, 999, 11)
expect(ev.payload_a).to_equal(11)
```

</details>

#### exit_event sets kind to ProcessExit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.exit_event(4, 100, 999, 0)
expect(ev.kind).to_equal(ProcessEventKind.ProcessExit.to_i32())
```

</details>

#### exit_event stores exit_code in payload_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.exit_event(4, 100, 999, 1)
expect(ev.payload_a).to_equal(1)
```

</details>

#### event_kind returns correct kind for syscall_entry event

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(1, 100, 999, 60, 0, 0)
val k = ev.event_kind()
expect(k.to_i32()).to_equal(0)
```

</details>

#### summary returns non-empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(1, 100, 999, 60, 0, 0)
val s = ev.summary()
expect(s.len()).to_be_greater_than(0)
```

</details>

### PageCheckpoint creation

#### create stores checkpoint_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create(5, 100)
expect(c.checkpoint_id).to_equal(5)
```

</details>

#### create stores event_seq

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create(5, 100)
expect(c.event_seq).to_equal(100)
```

</details>

#### create sets pid to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create(5, 100)
expect(c.pid).to_equal(0)
```

</details>

#### create starts with empty register_state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create(5, 100)
expect(c.register_state.len()).to_equal(0)
```

</details>

#### create starts with empty dirty_pages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create(5, 100)
expect(c.dirty_pages.len()).to_equal(0)
```

</details>

#### create_for_pid stores pid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create_for_pid(1, 50, 9876)
expect(c.pid).to_equal(9876)
```

</details>

#### create_for_pid stores event_seq

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create_for_pid(1, 50, 9876)
expect(c.event_seq).to_equal(50)
```

</details>

#### summary returns non-empty text

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create(3, 200)
val s = c.summary()
expect(s.len()).to_be_greater_than(0)
```

</details>

#### get_register returns None for unknown name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = PageCheckpoint.create(1, 10)
val found = c.get_register("rip")
match found:
    case None: expect(found.is_none()).to_equal(true)
    case Some(x): expect(false).to_equal(true)
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

#### latest returns None when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
val latest = mgr.latest()
match latest:
    case None: expect(latest.is_none()).to_equal(true)
    case Some(x): expect(false).to_equal(true)
```

</details>

#### find_checkpoint returns None for unknown id

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
val found = mgr.find_checkpoint(99)
match found:
    case None: expect(found.is_none()).to_equal(true)
    case Some(x): expect(false).to_equal(true)
```

</details>

#### nearest_before returns None when empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = CheckpointManager.create()
val found = mgr.nearest_before(1000)
match found:
    case None: expect(found.is_none()).to_equal(true)
    case Some(x): expect(false).to_equal(true)
```

</details>

### ChaosScheduler - empty runnable returns -1

#### Random returns -1 for empty list

1. var s = ChaosScheduler create
   - Expected: chosen equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.Random, 42)
val chosen = s.pick_next([])
expect(chosen).to_equal(-1)
```

</details>

#### RoundRobin returns -1 for empty list

1. var s = ChaosScheduler create
   - Expected: chosen equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.RoundRobin, 42)
val chosen = s.pick_next([])
expect(chosen).to_equal(-1)
```

</details>

#### StarveLast returns -1 for empty list

1. var s = ChaosScheduler create
   - Expected: chosen equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.StarveLast, 42)
val chosen = s.pick_next([])
expect(chosen).to_equal(-1)
```

</details>

#### PrioritizeNew returns -1 for empty list

1. var s = ChaosScheduler create
   - Expected: chosen equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.PrioritizeNew, 42)
val chosen = s.pick_next([])
expect(chosen).to_equal(-1)
```

</details>

### ChaosScheduler - single thread list

#### Random picks the only thread

1. var s = ChaosScheduler create
   - Expected: chosen equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.Random, 1)
val chosen = s.pick_next([99])
expect(chosen).to_equal(99)
```

</details>

#### RoundRobin picks the only thread

1. var s = ChaosScheduler create
   - Expected: chosen equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.RoundRobin, 1)
val chosen = s.pick_next([99])
expect(chosen).to_equal(99)
```

</details>

#### StarveLast picks the only thread

1. var s = ChaosScheduler create
   - Expected: chosen equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.StarveLast, 1)
val chosen = s.pick_next([99])
expect(chosen).to_equal(99)
```

</details>

#### PrioritizeNew picks the only thread

1. var s = ChaosScheduler create
   - Expected: chosen equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.PrioritizeNew, 1)
val chosen = s.pick_next([99])
expect(chosen).to_equal(99)
```

</details>

### ChaosScheduler - schedule_log grows

#### Random pick grows schedule_log by 1

1. var s = ChaosScheduler create
2. s pick next
   - Expected: s.schedule_log.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.Random, 7)
s.pick_next([1, 2, 3])
expect(s.schedule_log.len()).to_equal(1)
```

</details>

#### RoundRobin two picks grows schedule_log to 2

1. var s = ChaosScheduler create
2. s pick next
3. s pick next
   - Expected: s.schedule_log.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = ChaosScheduler.create(ChaosStrategy.RoundRobin, 7)
s.pick_next([10, 20])
s.pick_next([10, 20])
expect(s.schedule_log.len()).to_equal(2)
```

</details>

### ChaosStrategy to_i32 round-trips

#### Random to_i32 is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ChaosStrategy.Random.to_i32()).to_equal(0)
```

</details>

#### RoundRobin to_i32 is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ChaosStrategy.RoundRobin.to_i32()).to_equal(1)
```

</details>

#### StarveLast to_i32 is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ChaosStrategy.StarveLast.to_i32()).to_equal(2)
```

</details>

#### PrioritizeNew to_i32 is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ChaosStrategy.PrioritizeNew.to_i32()).to_equal(3)
```

</details>

#### from_i32 round-trips Random

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ChaosStrategy.from_i32(0)
expect(v.to_i32()).to_equal(0)
```

</details>

#### from_i32 round-trips PrioritizeNew

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ChaosStrategy.from_i32(3)
expect(v.to_i32()).to_equal(3)
```

</details>

#### from_i32 unknown falls back to Random

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = ChaosStrategy.from_i32(99)
expect(v.to_i32()).to_equal(0)
```

</details>

### ThreadRecorder initial state

#### switches list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tr = ThreadRecorder.create()
expect(tr.switches.len()).to_equal(0)
```

</details>

#### creates list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tr = ThreadRecorder.create()
expect(tr.creates.len()).to_equal(0)
```

</details>

#### active_threads is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tr = ThreadRecorder.create()
expect(tr.active_threads.len()).to_equal(0)
```

</details>

#### thread_count is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tr = ThreadRecorder.create()
expect(tr.thread_count()).to_equal(0)
```

</details>

#### switch_count is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tr = ThreadRecorder.create()
expect(tr.switch_count()).to_equal(0)
```

</details>

### ThreadRecorder on_thread_create

#### adds parent and child to active_threads

1. var tr = ThreadRecorder create
2. tr on thread create
   - Expected: tr.thread_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tr = ThreadRecorder.create()
tr.on_thread_create(1000, 1001, 9999)
expect(tr.thread_count()).to_equal(2)
```

</details>

#### records creates entry

1. var tr = ThreadRecorder create
2. tr on thread create
   - Expected: tr.creates.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tr = ThreadRecorder.create()
tr.on_thread_create(1000, 1001, 9999)
expect(tr.creates.len()).to_equal(1)
```

</details>

#### second child does not double-add parent

1. var tr = ThreadRecorder create
2. tr on thread create
3. tr on thread create
   - Expected: tr.thread_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tr = ThreadRecorder.create()
tr.on_thread_create(1000, 1001, 9999)
tr.on_thread_create(1000, 1002, 10000)
expect(tr.thread_count()).to_equal(3)
```

</details>

### ThreadRecorder on_thread_switch

#### records a switch event

1. var tr = ThreadRecorder create
2. tr on thread switch
   - Expected: tr.switch_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tr = ThreadRecorder.create()
tr.on_thread_switch(1000, 1001, 0, 5000)
expect(tr.switch_count()).to_equal(1)
```

</details>

#### get_schedule_order returns to_tid sequence

1. var tr = ThreadRecorder create
2. tr on thread switch
3. tr on thread switch
   - Expected: order.len() equals `2`
   - Expected: order[0] equals `20`
   - Expected: order[1] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tr = ThreadRecorder.create()
tr.on_thread_switch(10, 20, 0, 100)
tr.on_thread_switch(20, 30, 0, 200)
val order = tr.get_schedule_order()
expect(order.len()).to_equal(2)
expect(order[0]).to_equal(20)
expect(order[1]).to_equal(30)
```

</details>

### ThreadRecorder on_thread_exit

#### removes thread from active set

1. var tr = ThreadRecorder create
2. tr on thread create
3. tr on thread exit
   - Expected: tr.thread_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tr = ThreadRecorder.create()
tr.on_thread_create(1000, 1001, 100)
tr.on_thread_exit(1001, 200)
expect(tr.thread_count()).to_equal(1)
```

</details>

### ProcessReplayer initial state

#### events list is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessReplayer.create("/tmp/traces")
expect(r.events.len()).to_equal(0)
```

</details>

#### cursor starts at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessReplayer.create("/tmp/traces")
expect(r.cursor).to_equal(0)
```

</details>

#### total_matched starts at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessReplayer.create("/tmp/traces")
expect(r.total_matched).to_equal(0)
```

</details>

#### total_diverged starts at zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessReplayer.create("/tmp/traces")
expect(r.total_diverged).to_equal(0)
```

</details>

#### checkpoint_interval is 500

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessReplayer.create("/tmp/traces")
expect(r.checkpoint_interval).to_equal(500)
```

</details>

#### trace_dir field is stored

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ProcessReplayer.create("/tmp/traces")
expect(r.trace_dir).to_equal("/tmp/traces")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_process_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ProcessRecorder initial state
- ProcessEventKind variants
- ProcessReplayEvent constructors
- PageCheckpoint creation
- CheckpointManager
- ChaosScheduler - empty runnable returns -1
- ChaosScheduler - single thread list
- ChaosScheduler - schedule_log grows
- ChaosStrategy to_i32 round-trips
- ThreadRecorder initial state
- ThreadRecorder on_thread_create
- ThreadRecorder on_thread_switch
- ThreadRecorder on_thread_exit
- ProcessReplayer initial state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
