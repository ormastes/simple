# Replay Process Event Specification

> <details>

<!-- sdn-diagram:id=replay_process_event_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_process_event_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_process_event_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_process_event_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Process Event Specification

## Scenarios

### ProcessEventKind to_i32

#### SyscallEntry to_i32 returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ProcessEventKind.SyscallEntry
expect(k.to_i32()).to_equal(0)
```

</details>

#### SyscallExit to_i32 returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ProcessEventKind.SyscallExit
expect(k.to_i32()).to_equal(1)
```

</details>

#### Signal to_i32 returns 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ProcessEventKind.Signal
expect(k.to_i32()).to_equal(2)
```

</details>

#### ProcessExit to_i32 returns 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = ProcessEventKind.ProcessExit
expect(k.to_i32()).to_equal(9)
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

#### syscall_entry stores syscall number in payload_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_entry(1, 100, 999, 60, 0, 0)
expect(ev.payload_a).to_equal(60)
```

</details>

#### syscall_exit stores retval in payload_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_exit(2, 100, 1000, 42)
expect(ev.payload_a).to_equal(42)
```

</details>

#### signal_event sets kind to Signal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.signal_event(3, 200, 2000, 9)
expect(ev.kind).to_equal(ProcessEventKind.Signal.to_i32())
```

</details>

#### exit_event stores exit_code in payload_a

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.exit_event(4, 300, 3000, 1)
expect(ev.payload_a).to_equal(1)
```

</details>

#### event_kind() roundtrips for SyscallExit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ev = ProcessReplayEvent.syscall_exit(5, 1, 100, 0)
val k = ev.event_kind()
expect(k.to_i32()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_process_event_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ProcessEventKind to_i32
- ProcessReplayEvent constructors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
