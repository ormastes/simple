# Replay Process Facade Specification

> <details>

<!-- sdn-diagram:id=replay_process_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_process_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_process_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_process_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Process Facade Specification

## Scenarios

### nogc_async_mut replay process facades

#### re-exports event records and metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(1, 42, 99, 60, 3, 4)
val meta = ProcessTraceMetadata.create("echo hi")

expect(ev.kind).to_equal(ProcessEventKind.SyscallEntry.to_i32())
expect(ev.summary()).to_contain("syscall_entry")
expect(meta.command).to_equal("echo hi")
expect(PROCESS_EVENT_SIZE).to_equal(60)
```

</details>

#### re-exports recorder, replayer, and checkpoint types

1. var checkpoint = PageCheckpoint create
2. checkpoint add register
   - Expected: recorder.mode equals `RecordingMode.Idle`
   - Expected: replayer.event_count() equals `0`
   - Expected: checkpoint.get_register("pc") equals `Some(100)`
   - Expected: ReplayVerdict.Match.to_text() equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val recorder = ProcessRecorder.create("echo hi", "/tmp/simple-process-replay")
val replayer = ProcessReplayer.create("/tmp/simple-process-replay")
var checkpoint = PageCheckpoint.create(1, 10)
checkpoint.add_register("pc", 100)

expect(recorder.mode).to_equal(RecordingMode.Idle)
expect(replayer.event_count()).to_equal(0)
expect(checkpoint.get_register("pc")).to_equal(Some(100))
expect(ReplayVerdict.Match.to_text()).to_equal("match")
```

</details>

#### re-exports thread recorder and chaos scheduler

1. var threads = ThreadRecorder create
2. threads on thread create
3. threads on thread switch
4. var scheduler = ChaosScheduler create
   - Expected: threads.thread_count() equals `2`
   - Expected: threads.switch_count() equals `1`
   - Expected: chosen equals `11`
   - Expected: scheduler.schedule_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var threads = ThreadRecorder.create()
threads.on_thread_create(10, 11, 1)
threads.on_thread_switch(10, 11, 0, 2)

var scheduler = ChaosScheduler.create(ChaosStrategy.RoundRobin, 1)
val chosen = scheduler.pick_next([11, 12])

expect(threads.thread_count()).to_equal(2)
expect(threads.switch_count()).to_equal(1)
expect(chosen).to_equal(11)
expect(scheduler.schedule_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/replay/process/replay_process_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut replay process facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
