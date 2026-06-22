# Task Types Specification

> Tests for TaskId, TaskState, TaskPriority, TaskContext, and BlockReason kernel types. Validates construction and field access for all task-related structures used by the scheduler, IPC, and capability layers.

<!-- sdn-diagram:id=task_types_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=task_types_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

task_types_spec -> std
task_types_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=task_types_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Types Specification

Tests for TaskId, TaskState, TaskPriority, TaskContext, and BlockReason kernel types. Validates construction and field access for all task-related structures used by the scheduler, IPC, and capability layers.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-002 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/types/task_types_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for TaskId, TaskState, TaskPriority, TaskContext, and BlockReason
kernel types. Validates construction and field access for all task-related
structures used by the scheduler, IPC, and capability layers.

## Scenarios

### TaskId

#### stores the task identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = TaskId(id: 1)
expect(id.id).to_equal(1)
```

</details>

#### supports zero id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = TaskId(id: 0)
expect(id.id).to_equal(0)
```

</details>

#### supports large id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = TaskId(id: 999999)
expect(id.id).to_equal(999999)
```

</details>

#### can compare two equal ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = TaskId(id: 42)
val b = TaskId(id: 42)
expect(a.id).to_equal(b.id)
```

</details>

#### can distinguish different ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = TaskId(id: 1)
val b = TaskId(id: 2)
val same = a.id == b.id
expect(same).to_equal(false)
```

</details>

### TaskState

### Ready

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = TaskState.Ready
val is_ready = match state:
    TaskState.Ready: true
    _: false
expect(is_ready).to_equal(true)
```

</details>

### Running

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = TaskState.Running
val is_running = match state:
    TaskState.Running: true
    _: false
expect(is_running).to_equal(true)
```

</details>

### Blocked

#### can be constructed with IpcRecv reason

1. TaskState Blocked
   - Expected: is_blocked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = BlockReason.IpcRecv(port: 5)
val state = TaskState.Blocked(reason: reason)
val is_blocked = match state:
    TaskState.Blocked(reason): true
    _: false
expect(is_blocked).to_equal(true)
```

</details>

#### can be constructed with Sleep reason

1. TaskState Blocked
   - Expected: is_blocked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = BlockReason.Sleep(until_ns: 1000000)
val state = TaskState.Blocked(reason: reason)
val is_blocked = match state:
    TaskState.Blocked(reason): true
    _: false
expect(is_blocked).to_equal(true)
```

</details>

### Zombie

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = TaskState.Zombie
val is_zombie = match state:
    TaskState.Zombie: true
    _: false
expect(is_zombie).to_equal(true)
```

</details>

### TaskPriority

### Realtime

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prio = TaskPriority.Realtime
val is_rt = match prio:
    TaskPriority.Realtime: true
    _: false
expect(is_rt).to_equal(true)
```

</details>

### High

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prio = TaskPriority.High
val is_high = match prio:
    TaskPriority.High: true
    _: false
expect(is_high).to_equal(true)
```

</details>

### Normal

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prio = TaskPriority.Normal
val is_normal = match prio:
    TaskPriority.Normal: true
    _: false
expect(is_normal).to_equal(true)
```

</details>

### Low

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prio = TaskPriority.Low
val is_low = match prio:
    TaskPriority.Low: true
    _: false
expect(is_low).to_equal(true)
```

</details>

### Idle

#### can be constructed

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prio = TaskPriority.Idle
val is_idle = match prio:
    TaskPriority.Idle: true
    _: false
expect(is_idle).to_equal(true)
```

</details>

### BlockReason

#### IpcRecv carries port number

1. BlockReason IpcRecv
   - Expected: port_val equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = BlockReason.IpcRecv(port: 42)
val port_val = match reason:
    BlockReason.IpcRecv(port): port
    _: 0
expect(port_val).to_equal(42)
```

</details>

#### IpcSend carries port number

1. BlockReason IpcSend
   - Expected: port_val equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = BlockReason.IpcSend(port: 7)
val port_val = match reason:
    BlockReason.IpcSend(port): port
    _: 0
expect(port_val).to_equal(7)
```

</details>

#### Sleep carries timestamp

1. BlockReason Sleep
   - Expected: ts equals `5000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = BlockReason.Sleep(until_ns: 5000000)
val ts = match reason:
    BlockReason.Sleep(until_ns): until_ns
    _: 0
expect(ts).to_equal(5000000)
```

</details>

#### PageFault carries faulting address

1. BlockReason PageFault
   - Expected: fault_addr equals `0xDEAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = BlockReason.PageFault(addr: 0xDEAD)
val fault_addr = match reason:
    BlockReason.PageFault(addr): addr
    _: 0
expect(fault_addr).to_equal(0xDEAD)
```

</details>

#### Exit has no payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = BlockReason.Exit
val is_exit = match reason:
    BlockReason.Exit: true
    _: false
expect(is_exit).to_equal(true)
```

</details>

### TaskContext

#### stores general-purpose registers

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TaskContext(
    rax: 1, rbx: 2, rcx: 3, rdx: 4,
    rsi: 5, rdi: 6, rbp: 7, rsp: 8,
    r8: 9, r9: 10, r10: 11, r11: 12,
    r12: 13, r13: 14, r14: 15, r15: 16,
    rip: 0x1000, rflags: 0x202,
    cs: 0x23, ss: 0x1B, fpu_state: 0
)
expect(ctx.rax).to_equal(1)
expect(ctx.rbx).to_equal(2)
expect(ctx.rcx).to_equal(3)
expect(ctx.rdx).to_equal(4)
expect(ctx.rsi).to_equal(5)
expect(ctx.rdi).to_equal(6)
```

</details>

#### stores stack and instruction pointers

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0xFFFF0000, rsp: 0xFFFF1000,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0x401000, rflags: 0x202,
    cs: 0x23, ss: 0x1B, fpu_state: 0
)
expect(ctx.rbp).to_equal(0xFFFF0000)
expect(ctx.rsp).to_equal(0xFFFF1000)
expect(ctx.rip).to_equal(0x401000)
```

</details>

### UserProcessImage

#### stores executable path, entry, and stack

1. file bytes: [0x13 to u8
2. initial stack bytes: [0x01 to u8
   - Expected: image.binary_path equals `/sys/services/vfs`
   - Expected: image.entry equals `0x400000`
   - Expected: image.stack_top equals `0x4000000000`
   - Expected: user_process_image_segment_count(image) equals `0`
   - Expected: image.initial_sp equals `0x3fffffff80`
   - Expected: image.initial_stack_bytes.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = UserProcessImage(
    binary_path: "/sys/services/vfs",
    entry: 0x400000,
    stack_top: 0x4000000000,
    stack_size: 65536,
    argv: ["/sys/services/vfs"],
    envp: [],
    segments: [],
    segment_count: 0,
    file_bytes: [0x13.to_u8(), 0, 0, 0],
    initial_sp: 0x3fffffff80,
    initial_stack_bytes: [0x01.to_u8(), 0x02, 0x03, 0x04]
)
expect(image.binary_path).to_equal("/sys/services/vfs")
expect(image.entry).to_equal(0x400000)
expect(image.stack_top).to_equal(0x4000000000)
expect(user_process_image_segment_count(image)).to_equal(0)
expect(image.initial_sp).to_equal(0x3fffffff80)
expect(image.initial_stack_bytes.len()).to_equal(4)
```

</details>

#### stores loadable user segments

1. data: [0x13 to u8
   - Expected: seg.virt_addr equals `0x400000`
   - Expected: seg.data.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val seg = UserLoadSegment(
    virt_addr: 0x400000,
    mem_size: 4,
    file_size: 4,
    flags: 5,
    align: 0x1000,
    data: [0x13.to_u8(), 0, 0, 0]
)
expect(seg.virt_addr).to_equal(0x400000)
expect(seg.data.len()).to_equal(4)
```

</details>

#### stores segment selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0, rflags: 0x202,
    cs: 0x08, ss: 0x10, fpu_state: 0
)
expect(ctx.cs).to_equal(0x08)
expect(ctx.ss).to_equal(0x10)
```

</details>

#### stores rflags

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0, rflags: 0x202,
    cs: 0, ss: 0, fpu_state: 0
)
expect(ctx.rflags).to_equal(0x202)
```

</details>

#### stores extended registers r8-r15

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 100, r9: 200, r10: 300, r11: 400,
    r12: 500, r13: 600, r14: 700, r15: 800,
    rip: 0, rflags: 0,
    cs: 0, ss: 0, fpu_state: 0
)
expect(ctx.r8).to_equal(100)
expect(ctx.r9).to_equal(200)
expect(ctx.r10).to_equal(300)
expect(ctx.r11).to_equal(400)
expect(ctx.r12).to_equal(500)
expect(ctx.r13).to_equal(600)
expect(ctx.r14).to_equal(700)
expect(ctx.r15).to_equal(800)
```

</details>

#### stores fpu_state pointer

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = TaskContext(
    rax: 0, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0, rflags: 0,
    cs: 0, ss: 0, fpu_state: 0xBEEF0000
)
expect(ctx.fpu_state).to_equal(0xBEEF0000)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
