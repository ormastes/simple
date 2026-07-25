# Scheduler Specification

> Tests for the priority-based preemptive scheduler. Validates task creation, scheduling by priority, yield, block/unblock state transitions, and the ReadyQueue FIFO data structure.

<!-- sdn-diagram:id=scheduler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scheduler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scheduler_spec -> std
scheduler_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scheduler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 69 | 69 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scheduler Specification

Tests for the priority-based preemptive scheduler. Validates task creation, scheduling by priority, yield, block/unblock state transitions, and the ReadyQueue FIFO data structure.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-005 |
| Category | Runtime |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/scheduler/scheduler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the priority-based preemptive scheduler. Validates task creation,
scheduling by priority, yield, block/unblock state transitions, and the
ReadyQueue FIFO data structure.

Note: Timer interrupt handling and context switch are not testable without
hardware. We test the scheduling logic and state machine.

## Scenarios

### ReadyQueue

### construction

#### starts empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = ReadyQueue.new()
expect(q.is_empty()).to_equal(true)
```

</details>

#### has zero length

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = ReadyQueue.new()
expect(q.len()).to_equal(0)
```

</details>

### enqueue and dequeue

#### enqueue increases length

1. var q = ReadyQueue new

2. q enqueue
   - Expected: q.len() equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = ReadyQueue.new()
q.enqueue(TaskId(id: 1))
expect(q.len()).to_equal(1)
```

</details>

#### dequeue returns the enqueued task

1. var q = ReadyQueue new

2. q enqueue


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = ReadyQueue.new()
q.enqueue(TaskId(id: 42))
val result = q.dequeue()
expect(result).to_be_nil.to_equal(false)
```

</details>

#### dequeue preserves FIFO order

1. var q = ReadyQueue new

2. q enqueue

3. q enqueue

4. q enqueue
   - Expected: task.id equals `1`
   - Expected: task.id equals `2`
   - Expected: task.id equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = ReadyQueue.new()
q.enqueue(TaskId(id: 1))
q.enqueue(TaskId(id: 2))
q.enqueue(TaskId(id: 3))
val first = q.dequeue()
if first != nil:
    val task = first
    expect(task.id).to_equal(1)
val second = q.dequeue()
if second != nil:
    val task = second
    expect(task.id).to_equal(2)
val third = q.dequeue()
if third != nil:
    val task = third
    expect(task.id).to_equal(3)
```

</details>

#### dequeue from empty returns nil

1. var q = ReadyQueue new


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = ReadyQueue.new()
val result = q.dequeue()
expect(result).to_be_nil
```

</details>

#### is_empty after dequeue all

1. var q = ReadyQueue new

2. q enqueue

3. q dequeue
   - Expected: q.is_empty() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = ReadyQueue.new()
q.enqueue(TaskId(id: 1))
q.dequeue()
expect(q.is_empty()).to_equal(true)
```

</details>

### remove

#### removes specific task from queue

1. var q = ReadyQueue new

2. q enqueue

3. q enqueue

4. q enqueue

5. q remove
   - Expected: q.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = ReadyQueue.new()
q.enqueue(TaskId(id: 1))
q.enqueue(TaskId(id: 2))
q.enqueue(TaskId(id: 3))
q.remove(TaskId(id: 2))
expect(q.len()).to_equal(2)
```

</details>

#### preserves order after removal

1. var q = ReadyQueue new

2. q enqueue

3. q enqueue

4. q enqueue

5. q remove
   - Expected: task.id equals `10`
   - Expected: task.id equals `30`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var q = ReadyQueue.new()
q.enqueue(TaskId(id: 10))
q.enqueue(TaskId(id: 20))
q.enqueue(TaskId(id: 30))
q.remove(TaskId(id: 20))
val first = q.dequeue()
if first != nil:
    val task = first
    expect(task.id).to_equal(10)
val second = q.dequeue()
if second != nil:
    val task = second
    expect(task.id).to_equal(30)
```

</details>

### Scheduler

### construction

#### starts with empty task table

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = Scheduler.new()
val task = sched.get_task(TaskId(id: 0))
expect(task).to_be_nil
```

</details>

#### starts with current task id 0

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = Scheduler.new()
val current = sched.get_current()
expect(current.id).to_equal(0)
```

</details>

#### starts with tick count 0

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = Scheduler.new()
expect(sched.get_tick_count()).to_equal(0)
```

</details>

#### builds ARM user contexts for executable images

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arm64_ctx = scheduler_user_context_for_arch(Architecture.Arm64, 0x400000, 0x3FFFFFFF80)
expect(arm64_ctx.rip).to_equal(0x400000)
expect(arm64_ctx.rsp).to_equal(0x3FFFFFFF80)
expect(arm64_ctx.rflags).to_equal(0)
expect(arm64_ctx.cs).to_equal(0)
expect(arm64_ctx.ss).to_equal(0)

val arm32_ctx = scheduler_user_context_for_arch(Architecture.Arm32, 0x80000000, 0x81000000)
expect(arm32_ctx.rip).to_equal(0x80000000)
expect(arm32_ctx.rsp).to_equal(0x81000000)
expect(arm32_ctx.rflags).to_equal(0x10)
expect(arm32_ctx.cs).to_equal(0)
expect(arm32_ctx.ss).to_equal(0)
```

</details>

#### builds x86 user contexts for executable images

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86_64_ctx = scheduler_user_context_for_arch(Architecture.X86_64, 0x400000, 0x7FFFFFFFFFEF)
expect(x86_64_ctx.rip).to_equal(0x400000)
expect(x86_64_ctx.rsp).to_equal(0x7FFFFFFFFFE0)
expect(x86_64_ctx.rbp).to_equal(0x7FFFFFFFFFE0)
expect(x86_64_ctx.rflags).to_equal(0x202)
expect(x86_64_ctx.cs).to_equal(0x1B)
expect(x86_64_ctx.ss).to_equal(0x23)

val x86_32_ctx = scheduler_user_context_for_arch(Architecture.X86, 0x8048000, 0xBFFFFFEF)
expect(x86_32_ctx.rip).to_equal(0x8048000)
expect(x86_32_ctx.rsp).to_equal(0xBFFFFFE0)
expect(x86_32_ctx.rbp).to_equal(0xBFFFFFE0)
expect(x86_32_ctx.rflags).to_equal(0x202)
expect(x86_32_ctx.cs).to_equal(0x1B)
expect(x86_32_ctx.ss).to_equal(0x23)
```

</details>

#### starts with an explicit flat topology domain

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = Scheduler.new()
val topology = default_scheduler_topology(32u32)
expect(sched.topology_cpu_count()).to_equal(32u32)
expect(sched.topology_domain_count()).to_equal(1)
expect(topology.domains[0].kind).to_equal(SchedulerDomainKind.Flat)
expect(topology.domains[0].rebalance_threshold).to_equal(2)
```

</details>

### green carrier scheduler integration

#### stores green execution state through scheduler-owned hook

1. var sched = Scheduler new with cpu count
   - Expected: result.applied is true
   - Expected: sched.green_current_task_on_cpu(1u32) equals `41`
   - Expected: sched.green_context_switches_on_cpu(1u32) equals `1`
   - Expected: sched.green_rejected_intents() equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(41, 4, 0, 3, 1, 2, 4, 1)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 1)
val result = sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))
expect(result.applied).to_equal(true)
expect(sched.green_current_task_on_cpu(1u32)).to_equal(41)
expect(sched.green_context_switches_on_cpu(1u32)).to_equal(1)
expect(sched.green_rejected_intents()).to_equal(0)
```

</details>

#### keeps normal current task separate from green lane

1. var sched = Scheduler new with cpu count

2. sched apply green scheduler intent
   - Expected: sched.get_current_on_cpu(0u32).id equals `0`
   - Expected: sched.green_current_task_on_cpu(1u32) equals `88`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(4u32)
val normal_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(88, 4, 0, 3, 1, 2, 4, 1)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 1)
sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))
expect(normal_id.id).to_be_greater_than(0)
expect(sched.get_current_on_cpu(0u32).id).to_equal(0)
expect(sched.green_current_task_on_cpu(1u32)).to_equal(88)
```

</details>

#### extends green execution slots when topology grows

1. var sched = Scheduler new bootstrap

2. sched set topology

3. sched apply green scheduler intent
   - Expected: sched.green_current_task_on_cpu(3u32) equals `77`
   - Expected: sched.green_context_switches_on_cpu(3u32) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_bootstrap()
sched.set_topology(default_scheduler_topology(4u32))
val queues = green_carrier_run_queues_new(4, 8)
val decision = green_carrier_spawn_task(77, 4, 8, 3, 1, 2, 4, 0)
val queued = green_carrier_apply_enqueue(queues, decision)
val dispatched = green_carrier_dispatch_next(queued.queues, 3)
sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))
expect(sched.green_current_task_on_cpu(3u32)).to_equal(77)
expect(sched.green_context_switches_on_cpu(3u32)).to_equal(1)
```

</details>

#### records rejected green intent without touching normal current task

1. var sched = Scheduler new with cpu count
   - Expected: result.applied is false
   - Expected: sched.green_rejected_intents() equals `1`
   - Expected: sched.get_current_on_cpu(0u32).id equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_with_cpu_count(2u32)
val normal_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val queues = green_carrier_run_queues_new(2, 8)
val dispatched = green_carrier_dispatch_next(queues, 1)
val result = sched.apply_green_scheduler_intent(green_carrier_scheduler_intent(dispatched))
expect(result.applied).to_equal(false)
expect(normal_id.id).to_be_greater_than(0)
expect(sched.green_rejected_intents()).to_equal(1)
expect(sched.get_current_on_cpu(0u32).id).to_equal(0)
```

</details>

### create_task

#### returns a valid TaskId

1. var sched = Scheduler new


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val caps = CapabilitySet.full()
val id = sched.create_task(0x1000, TaskPriority.Normal, caps)
expect(id.id).to_be_greater_than(0)
```

</details>

#### assigns sequential task ids

1. var sched = Scheduler new
   - Expected: id2.id equals `id1.id + 1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val caps1 = CapabilitySet.full()
val caps2 = CapabilitySet.full()
val id1 = sched.create_task(0x1000, TaskPriority.Normal, caps1)
val id2 = sched.create_task(0x2000, TaskPriority.Normal, caps2)
expect(id2.id).to_equal(id1.id + 1)
```

</details>

#### creates task in Ready state

1. var sched = Scheduler new
   - Expected: is_ready is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val caps = CapabilitySet.full()
val id = sched.create_task(0x1000, TaskPriority.Normal, caps)
val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
```

</details>

#### stores the entry point in rip

1. var sched = Scheduler new
   - Expected: task.context.rip equals `0xDEAD`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val caps = CapabilitySet.full()
val id = sched.create_task(0xDEAD, TaskPriority.Normal, caps)
val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    expect(task.context.rip).to_equal(0xDEAD)
```

</details>

#### stores the priority

1. var sched = Scheduler new
   - Expected: is_high is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val caps = CapabilitySet.full()
val id = sched.create_task(0x1000, TaskPriority.High, caps)
val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_high = match task.priority:
        TaskPriority.High: true
        _: false
    expect(is_high).to_equal(true)
```

</details>

### create_user_task

#### creates user tasks with user mode markers

1. var sched = Scheduler new

2. data: [0x13 to u8

3. file bytes: [0x13 to u8

4. initial stack bytes: [0x01 to u8
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x400000`
   - Expected: task.user_stack equals `0x4000000000`
   - Expected: has_user_context equals `1`
   - Expected: user_ctx.rip equals `0x400000`
   - Expected: user_ctx.rsp equals `0x3fffffff80`
   - Expected: user_ctx.rbp equals `0x3fffffff80`
   - Expected: user_ctx.rflags equals `0x202`
   - Expected: user_ctx.cs equals `0x23`
   - Expected: user_ctx.ss equals `0x1B`
   - Expected: task.context.rsp equals `0x3fffffff80`
   - Expected: task.context.rbp equals `0x3fffffff80`


<details>
<summary>Executable SPipe</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val image = UserProcessImage(
    binary_path: "/sys/services/vfs",
    entry: 0x400000,
    stack_top: 0x4000000000,
    stack_size: 65536,
    argv: ["/sys/services/vfs"],
    envp: [],
    segments: [UserLoadSegment(
        virt_addr: 0x400000,
        mem_size: 4,
        file_size: 4,
        flags: 5,
        align: 0x1000,
        data: [0x13.to_u8(), 0, 0, 0]
    )],
    segment_count: 1,
    file_bytes: [0x13.to_u8(), 0, 0, 0],
    initial_sp: 0x3fffffff80,
    initial_stack_bytes: [0x01.to_u8(), 0x02, 0x03, 0x04]
)
val id = sched.create_user_task(image, TaskPriority.High, CapabilitySet.full())
expect(id.id).to_be_greater_than(0)
val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x400000)
    expect(task.user_stack).to_equal(0x4000000000)
    val has_user_context = if task.user_context == nil: 0 else: 1
    expect(has_user_context).to_equal(1)
    if val user_ctx = task.user_context:
        expect(user_ctx.rip).to_equal(0x400000)
        expect(user_ctx.rsp).to_equal(0x3fffffff80)
        expect(user_ctx.rbp).to_equal(0x3fffffff80)
        expect(user_ctx.rflags).to_equal(0x202)
        expect(user_ctx.cs).to_equal(0x23)
        expect(user_ctx.ss).to_equal(0x1B)
    expect(task.context.rsp).to_equal(0x3fffffff80)
    expect(task.context.rbp).to_equal(0x3fffffff80)
```

</details>

#### creates a bootstrap user task in slot zero

1. var sched = Scheduler new bootstrap

2. data: [0x13 to u8

3. file bytes: [0x13 to u8

4. initial stack bytes: [0x01 to u8
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x400000`
   - Expected: task.user_stack equals `0x4000000000`
   - Expected: handoff.id.id equals `pid`
   - Expected: handoff.user_context == nil is false
   - Expected: newest_handoff.id.id equals `pid`


<details>
<summary>Executable SPipe</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new_bootstrap()
val image = UserProcessImage(
    binary_path: "/sys/apps/hello_world.smf",
    entry: 0x400000,
    stack_top: 0x4000000000,
    stack_size: 65536,
    argv: ["/sys/apps/hello_world.smf"],
    envp: [],
    segments: [UserLoadSegment(
        virt_addr: 0x400000,
        mem_size: 4,
        file_size: 4,
        flags: 5,
        align: 0x1000,
        data: [0x13.to_u8(), 0, 0, 0]
    )],
    segment_count: 1,
    file_bytes: [0x13.to_u8(), 0, 0, 0],
    initial_sp: 0x3fffffff80,
    initial_stack_bytes: [0x01.to_u8(), 0x02, 0x03, 0x04]
)
val pid = sched.create_bootstrap_user_task_pid(image, TaskPriority.Normal, CapabilitySet.full())
expect(pid).to_be_greater_than(0)
val tcb = sched.get_task(TaskId(id: pid))
if tcb != nil:
    val task = tcb
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x400000)
    expect(task.user_stack).to_equal(0x4000000000)
val handoff = sched.get_user_handoff_task(pid)
if handoff != nil:
    expect(handoff.id.id).to_equal(pid)
    expect(handoff.user_context == nil).to_equal(false)
val newest_handoff = sched.get_user_handoff_task(0)
if newest_handoff != nil:
    expect(newest_handoff.id.id).to_equal(pid)
```

</details>

#### exec_image replaces the image while preserving task id

1. var sched = Scheduler new

2. data: [0x13 to u8

3. file bytes: [0x13 to u8

4. initial stack bytes: [0x01 to u8
   - Expected: sched.exec_image(id, image) equals `0`
   - Expected: task.id.id equals `id.id`
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x500000`
   - Expected: task.user_stack equals `0x5000000000`
   - Expected: user_ctx.rip equals `0x500000`
   - Expected: user_ctx.rsp equals `0x4fffffff80`


<details>
<summary>Executable SPipe</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val image = UserProcessImage(
    binary_path: "/bin/new",
    entry: 0x500000,
    stack_top: 0x5000000000,
    stack_size: 65536,
    argv: ["/bin/new"],
    envp: [],
    segments: [UserLoadSegment(
        virt_addr: 0x500000,
        mem_size: 4,
        file_size: 4,
        flags: 5,
        align: 0x1000,
        data: [0x13.to_u8(), 0, 0, 0]
    )],
    segment_count: 1,
    file_bytes: [0x13.to_u8(), 0, 0, 0],
    initial_sp: 0x4fffffff80,
    initial_stack_bytes: [0x01.to_u8(), 0x02, 0x03, 0x04]
)

expect(sched.exec_image(id, image)).to_equal(0)
val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    expect(task.id.id).to_equal(id.id)
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x500000)
    expect(task.user_stack).to_equal(0x5000000000)
    if val user_ctx = task.user_context:
        expect(user_ctx.rip).to_equal(0x500000)
        expect(user_ctx.rsp).to_equal(0x4fffffff80)
```

</details>

#### exec_into resolves argv0 and replaces the task image

1.  clear synthetic initramfs for test

2.  set synthetic initramfs for test

3. var sched = Scheduler new
   - Expected: result equals `0`
   - Expected: task.id.id equals `id.id`
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x400000`
   - Expected: user_ctx.rip equals `0x400000`

4.  clear synthetic initramfs for test


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_initramfs_for_test()
_set_synthetic_initramfs_for_test("/usr/bin/scheduler_exec_probe", _make_x86_64_exec())
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

val result = sched.exec_into(id, ["/usr/bin/scheduler_exec_probe"], [])

expect(result).to_equal(0)
val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    expect(task.id.id).to_equal(id.id)
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x400000)
    if val user_ctx = task.user_context:
        expect(user_ctx.rip).to_equal(0x400000)
_clear_synthetic_initramfs_for_test()
```

</details>

### multiple tasks with different priorities

#### can create tasks at all priority levels

1. var sched = Scheduler new


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val rt = sched.create_task(0x1000, TaskPriority.Realtime, CapabilitySet.full())
val hi = sched.create_task(0x2000, TaskPriority.High, CapabilitySet.full())
val nm = sched.create_task(0x3000, TaskPriority.Normal, CapabilitySet.full())
val lo = sched.create_task(0x4000, TaskPriority.Low, CapabilitySet.full())
val id = sched.create_task(0x5000, TaskPriority.Idle, CapabilitySet.full())
# All should have valid ids
expect(rt.id).to_be_greater_than(0)
expect(hi.id).to_be_greater_than(0)
expect(nm.id).to_be_greater_than(0)
expect(lo.id).to_be_greater_than(0)
expect(id.id).to_be_greater_than(0)
```

</details>

#### initializes scheduler policy metadata from legacy priority

1. var sched = Scheduler new
   - Expected: code equals `0`
   - Expected: task.isolation.sandboxed is true
   - Expected: code equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val normal_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val low_id = sched.create_task(0x2000, TaskPriority.Low, CapabilitySet.full())
val normal = sched.get_task(normal_id)
val low = sched.get_task(low_id)
if normal != nil:
    val task = normal
    val code = match task.schedule.policy:
        case Fair: 0
        case _: 1
    expect(code).to_equal(0)
    expect(task.isolation.sandboxed).to_equal(true)
if low != nil:
    val task = low
    val code = match task.schedule.policy:
        case Background: 0
        case _: 1
    expect(code).to_equal(0)
```

</details>

### schedule

#### picks highest priority task

1. var sched = Scheduler new
   - Expected: current.id equals `hi_id.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val lo_id = sched.create_task(0x1000, TaskPriority.Low, CapabilitySet.full())
val hi_id = sched.create_task(0x2000, TaskPriority.High, CapabilitySet.full())
val nm_id = sched.create_task(0x3000, TaskPriority.Normal, CapabilitySet.full())

# schedule() should pick High first
val ctx = sched.schedule()
val current = sched.get_current()
expect(current.id).to_equal(hi_id.id)
```

</details>

#### picks Realtime over Normal

1. var sched = Scheduler new
   - Expected: current.id equals `rt_id.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val nm_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val rt_id = sched.create_task(0x2000, TaskPriority.Realtime, CapabilitySet.full())

val ctx = sched.schedule()
val current = sched.get_current()
expect(current.id).to_equal(rt_id.id)
```

</details>

#### picks highest fixed-priority realtime task before FIFO order

1. var sched = Scheduler new

2. var low cfg = default task schedule

3. var high cfg = default task schedule

4. sched set schedule config

5. sched set schedule config
   - Expected: current.id equals `high_rt.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val low_rt = sched.create_task(0x1000, TaskPriority.Realtime, CapabilitySet.full())
val high_rt = sched.create_task(0x2000, TaskPriority.Realtime, CapabilitySet.full())
var low_cfg = default_task_schedule(TaskPriority.Realtime)
low_cfg.priority = 60
var high_cfg = default_task_schedule(TaskPriority.Realtime)
high_cfg.priority = 10
sched.set_schedule_config(low_rt, low_cfg)
sched.set_schedule_config(high_rt, high_cfg)

val ctx = sched.schedule()
val current = sched.get_current()
expect(current.id).to_equal(high_rt.id)
```

</details>

#### admits deadline task and schedules it before realtime

1. var sched = Scheduler new
   - Expected: result equals `0`
   - Expected: tcb.schedule.policy equals `SchedulerPolicy.Deadline`
   - Expected: tcb.schedule.runtime_ns equals `100000`
   - Expected: tcb.schedule.period_ns equals `1000000`
   - Expected: tcb.schedule.deadline_ns equals `500000`
   - Expected: current.id equals `dl_id.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val rt_id = sched.create_task(0x1000, TaskPriority.Realtime, CapabilitySet.full())
val dl_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val result = sched.admit_deadline(dl_id, 100000, 1000000, 500000, 0)
expect(result).to_equal(0)

val task = sched.get_task(dl_id)
if task != nil:
    val tcb = task
    expect(tcb.schedule.policy).to_equal(SchedulerPolicy.Deadline)
    expect(tcb.schedule.runtime_ns).to_equal(100000)
    expect(tcb.schedule.period_ns).to_equal(1000000)
    expect(tcb.schedule.deadline_ns).to_equal(500000)

val ctx = sched.schedule()
val current = sched.get_current()
expect(current.id).to_equal(dl_id.id)
```

</details>

#### picks admitted deadline task with earliest deadline

1. var sched = Scheduler new
   - Expected: later equals `0`
   - Expected: earlier equals `0`
   - Expected: current.id equals `earlier_id.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val later_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val earlier_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val later = sched.admit_deadline(later_id, 100000, 1000000, 900000, 0)
val earlier = sched.admit_deadline(earlier_id, 100000, 1000000, 200000, 0)
expect(later).to_equal(0)
expect(earlier).to_equal(0)

val ctx = sched.schedule()
val current = sched.get_current()
expect(current.id).to_equal(earlier_id.id)
```

</details>

#### rejects invalid and overcommitted deadline admission

1. var sched = Scheduler new
   - Expected: bad equals `-22`
   - Expected: overloaded equals `-28`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val invalid_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val overloaded_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val bad = sched.admit_deadline(invalid_id, 800000, 1000000, 400000, 1)
expect(bad).to_equal(-22)
val overloaded = sched.admit_deadline(overloaded_id, 900000, 1000000, 900000, 1)
expect(overloaded).to_equal(-28)
```

</details>

#### picks fair task with earliest virtual deadline

1. var sched = Scheduler new

2. var slow cfg = default task schedule

3. var fast cfg = default task schedule

4. sched set schedule config

5. sched set schedule config
   - Expected: current.id equals `fast_id.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val slow_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val fast_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
var slow_cfg = default_task_schedule(TaskPriority.Normal)
slow_cfg.virtual_deadline = 100
var fast_cfg = default_task_schedule(TaskPriority.Normal)
fast_cfg.virtual_deadline = 10
sched.set_schedule_config(slow_id, slow_cfg)
sched.set_schedule_config(fast_id, fast_cfg)
val ctx = sched.schedule()
val current = sched.get_current()
expect(current.id).to_equal(fast_id.id)
```

</details>

#### schedules from the selected CPU run queue

1. var sched = Scheduler new

2. var cfg = default task schedule

3. sched set schedule config
   - Expected: current.id equals `cpu1_id.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val cpu0_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val cpu1_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
var cfg = default_task_schedule(TaskPriority.Normal)
cfg.home_cpu = 1u32
cfg.virtual_deadline = 1
sched.set_schedule_config(cpu1_id, cfg)

val ctx = sched.schedule_on_cpu(1u32)
val current = sched.get_current()
expect(current.id).to_equal(cpu1_id.id)
```

</details>

#### rebalances one fair task from busiest to idlest CPU

1. var sched = Scheduler new
   - Expected: moved is true
   - Expected: sched.cpu_runnable_count(0u32) equals `2`
   - Expected: sched.cpu_runnable_count(1u32) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id1 = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val id2 = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val id3 = sched.create_task(0x3000, TaskPriority.Normal, CapabilitySet.full())

val moved = sched.rebalance_once()
expect(moved).to_equal(true)
expect(sched.cpu_runnable_count(0u32)).to_equal(2)
expect(sched.cpu_runnable_count(1u32)).to_equal(1)
```

</details>

#### does not rebalance below the topology threshold

1. var sched = Scheduler new
   - Expected: moved is false
   - Expected: sched.cpu_runnable_count(0u32) equals `1`
   - Expected: sched.cpu_runnable_count(1u32) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id1 = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val moved = sched.rebalance_once()
expect(moved).to_equal(false)
expect(sched.cpu_runnable_count(0u32)).to_equal(1)
expect(sched.cpu_runnable_count(1u32)).to_equal(0)
```

</details>

#### unblock path triggers one rebalance after threshold imbalance

1. var sched = Scheduler new

2. sched block task

3. sched unblock task
   - Expected: sched.cpu_runnable_count(0u32) equals `2`
   - Expected: sched.cpu_runnable_count(1u32) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val sleeper = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val load1 = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val load2 = sched.create_task(0x3000, TaskPriority.Normal, CapabilitySet.full())

sched.block_task(sleeper, BlockReason.Sleep(until_ns: 10000000))
sched.unblock_task(sleeper)

expect(sched.cpu_runnable_count(0u32)).to_equal(2)
expect(sched.cpu_runnable_count(1u32)).to_equal(1)
```

</details>

#### wake-affine placement follows the current CPU when load is close

1. var sched = Scheduler new

2. var waker cfg = default task schedule

3. sched set schedule config

4. sched block task

5. sched schedule on cpu

6. sched unblock task
   - Expected: task.assigned_cpu equals `1u32`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val sleeper = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val waker = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())

var waker_cfg = default_task_schedule(TaskPriority.Normal)
waker_cfg.home_cpu = 1u32
waker_cfg.virtual_deadline = 1
sched.set_schedule_config(waker, waker_cfg)
sched.block_task(sleeper, BlockReason.Sleep(until_ns: 10000000))
sched.schedule_on_cpu(1u32)

sched.unblock_task(sleeper)

val tcb = sched.get_task(sleeper)
if tcb != nil:
    val task = tcb
    expect(task.assigned_cpu).to_equal(1u32)
```

</details>

#### wake-affine placement keeps home CPU when the waker CPU is overloaded

1. var sched = Scheduler new

2. var waker cfg = default task schedule

3. sched set schedule config

4. var load cfg = default task schedule

5. sched set schedule config

6. sched set schedule config

7. sched set schedule config

8. sched block task

9. sched schedule on cpu

10. sched unblock task
   - Expected: task.assigned_cpu equals `0u32`


<details>
<summary>Executable SPipe</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val sleeper = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val waker = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val load1 = sched.create_task(0x3000, TaskPriority.Normal, CapabilitySet.full())
val load2 = sched.create_task(0x4000, TaskPriority.Normal, CapabilitySet.full())
val load3 = sched.create_task(0x5000, TaskPriority.Normal, CapabilitySet.full())

var waker_cfg = default_task_schedule(TaskPriority.Normal)
waker_cfg.home_cpu = 1u32
waker_cfg.virtual_deadline = 1
sched.set_schedule_config(waker, waker_cfg)

var load_cfg = default_task_schedule(TaskPriority.Normal)
load_cfg.home_cpu = 1u32
sched.set_schedule_config(load1, load_cfg)
sched.set_schedule_config(load2, load_cfg)
sched.set_schedule_config(load3, load_cfg)

sched.block_task(sleeper, BlockReason.Sleep(until_ns: 10000000))
sched.schedule_on_cpu(1u32)
sched.unblock_task(sleeper)

val tcb = sched.get_task(sleeper)
if tcb != nil:
    val task = tcb
    expect(task.assigned_cpu).to_equal(0u32)
```

</details>

#### tracks current task per CPU and records wakeup preemption

1. var sched = Scheduler new

2. var run cfg = default task schedule

3. sched set schedule config

4. var wake cfg = default task schedule

5. sched set schedule config

6. sched block task

7. sched schedule on cpu
   - Expected: decision.should_preempt is true
   - Expected: decision.reason equals `SchedulerPreemptionReason.EarlierVirtualDeadline`
   - Expected: task.id equals `sleeper.id`
   - Expected: sched.trace_event_count(SchedulerTraceKind.WakePreempt) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val running = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val sleeper = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
var run_cfg = default_task_schedule(TaskPriority.Normal)
run_cfg.virtual_deadline = 1000
sched.set_schedule_config(running, run_cfg)
var wake_cfg = default_task_schedule(TaskPriority.Normal)
wake_cfg.virtual_deadline = 10
sched.set_schedule_config(sleeper, wake_cfg)
sched.block_task(sleeper, BlockReason.Sleep(until_ns: 10000000))
sched.schedule_on_cpu(0u32)

val decision = sched.unblock_task_on_cpu(sleeper, 0u32)

expect(decision.should_preempt).to_equal(true)
expect(decision.reason).to_equal(SchedulerPreemptionReason.EarlierVirtualDeadline)
val pending = sched.preempt_pending_on_cpu(0u32)
if pending != nil:
    val task = pending
    expect(task.id).to_equal(sleeper.id)
expect(sched.trace_event_count(SchedulerTraceKind.WakePreempt)).to_equal(1)
```

</details>

#### idle balance pulls one fair task and traces the pull

1. var sched = Scheduler new
   - Expected: moved is true
   - Expected: sched.cpu_runnable_count(1u32) equals `1`
   - Expected: sched.trace_event_count(SchedulerTraceKind.IdlePull) equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id1 = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

val moved = sched.idle_balance_once(1u32)

expect(moved).to_equal(true)
expect(sched.cpu_runnable_count(1u32)).to_equal(1)
expect(sched.trace_event_count(SchedulerTraceKind.IdlePull)).to_equal(1)
```

</details>

#### rt budget throttling allows fair tasks to run

1. var sched = Scheduler new
   - Expected: sched.configure_rt_bandwidth(0u32, 10000000, 30000000) equals `0`

2. sched schedule

3. sched timer tick
   - Expected: sched.rt_throttled(0u32) is true
   - Expected: sched.get_current().id equals `fair_id.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
expect(sched.configure_rt_bandwidth(0u32, 10000000, 30000000)).to_equal(0)
val rt_id = sched.create_task(0x1000, TaskPriority.Realtime, CapabilitySet.full())
val fair_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())

sched.schedule()
val rt_task = sched.get_task(rt_id)
if rt_task != nil:
    val task = rt_task
    sched.timer_tick(task.context)

expect(sched.rt_throttled(0u32)).to_equal(true)
val ctx = sched.schedule()
expect(sched.get_current().id).to_equal(fair_id.id)
expect(sched.trace_event_count(SchedulerTraceKind.RtThrottle)).to_be_greater_than(0)
```

</details>

#### priority inheritance boosts and restores mutex owner priority

1. var sched = Scheduler new

2. var owner cfg = default task schedule

3. var waiter cfg = default task schedule

4. sched set schedule config

5. sched set schedule config

6. var mutex = PiMutex new

7. mutex = sched pi mutex lock

8. mutex = sched pi mutex lock
   - Expected: task.schedule.priority equals `10`

9. mutex = sched pi mutex unlock
   - Expected: task.schedule.priority equals `50`


<details>
<summary>Executable SPipe</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val owner = sched.create_task(0x1000, TaskPriority.Realtime, CapabilitySet.full())
val waiter = sched.create_task(0x2000, TaskPriority.Realtime, CapabilitySet.full())
var owner_cfg = default_task_schedule(TaskPriority.Realtime)
owner_cfg.priority = 50
var waiter_cfg = default_task_schedule(TaskPriority.Realtime)
waiter_cfg.priority = 10
sched.set_schedule_config(owner, owner_cfg)
sched.set_schedule_config(waiter, waiter_cfg)
var mutex = PiMutex.new()
mutex = sched.pi_mutex_lock(mutex, owner)
mutex = sched.pi_mutex_lock(mutex, waiter)

val boosted = sched.get_task(owner)
if boosted != nil:
    val task = boosted
    expect(task.schedule.priority).to_equal(10)

mutex = sched.pi_mutex_unlock(mutex, owner)
val restored = sched.get_task(owner)
if restored != nil:
    val task = restored
    expect(task.schedule.priority).to_equal(50)
```

</details>

#### deadline CBS records overrun and miss traces

1. var sched = Scheduler new
   - Expected: sched.admit_deadline(dl_id, 10000000, 10000000, 10000000, 0) equals `0`

2. sched schedule

3. sched timer tick

4. sched timer tick


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val dl_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
expect(sched.admit_deadline(dl_id, 10000000, 10000000, 10000000, 0)).to_equal(0)
sched.schedule()
val dl_task = sched.get_task(dl_id)
if dl_task != nil:
    val task = dl_task
    sched.timer_tick(task.context)
    sched.timer_tick(task.context)

expect(sched.trace_event_count(SchedulerTraceKind.DeadlineOverrun)).to_be_greater_than(0)
expect(sched.deadline_miss_count(dl_id)).to_be_greater_than(0)
```

</details>

### process isolation

#### monotonically restricts isolation metadata

1. var sched = Scheduler new
   - Expected: ok is true
   - Expected: task.isolation.capability_generation equals `2`
   - Expected: task.isolation.allow_network is false
   - Expected: task.isolation.max_memory_pages equals `128`


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val ok = sched.restrict_isolation(id, false, 128, 1u32)
expect(ok).to_equal(true)
val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    expect(task.isolation.capability_generation).to_equal(2)
    expect(task.isolation.allow_network).to_equal(false)
    expect(task.isolation.max_memory_pages).to_equal(128)
```

</details>

### fair accounting

#### advances virtual runtime and deadline on timer tick

1. var sched = Scheduler new

2. sched schedule

3. sched timer tick


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
sched.schedule()
val before = sched.get_task(id)
if before != nil:
    val task_before = before
    sched.timer_tick(task_before.context)
val after = sched.get_task(id)
if after != nil:
    val task_after = after
    expect(task_after.schedule.vruntime).to_be_greater_than(0)
    expect(task_after.schedule.virtual_deadline).to_be_greater_than(task_after.schedule.requested_slice_ns.to_i64())
```

</details>

#### timer tick reschedules when current task was blocked

1. var sched = Scheduler new

2. sched schedule

3. sched block task

4. sched timer tick
   - Expected: sched.get_current().id equals `next_id.id`

5. TaskState Blocked
   - Expected: is_blocked is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val blocked_id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val next_id = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
sched.schedule()

val before = sched.get_task(blocked_id)
if before != nil:
    val task_before = before
    sched.block_task(blocked_id, BlockReason.Sleep(until_ns: 100000000))
    sched.timer_tick(task_before.context)

expect(sched.get_current().id).to_equal(next_id.id)
val blocked = sched.get_task(blocked_id)
if blocked != nil:
    val blocked_task = blocked
    val is_blocked = match blocked_task.state:
        TaskState.Blocked(reason): true
        _: false
    expect(is_blocked).to_equal(true)
```

</details>

### yield_current

#### moves current task back to ready

1. var sched = Scheduler new

2. sched schedule

3. sched yield current
   - Expected: is_ready is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

# Schedule the task (makes it Running)
sched.schedule()

# Yield should put it back in ready queue
sched.yield_current()

val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
```

</details>

### block_task and unblock_task

#### block sets task to Blocked state

1. var sched = Scheduler new

2. sched block task

3. TaskState Blocked
   - Expected: is_blocked is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

sched.block_task(id, BlockReason.IpcRecv(port: 1))

val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_blocked = match task.state:
        TaskState.Blocked(reason): true
        _: false
    expect(is_blocked).to_equal(true)
```

</details>

#### unblock sets task back to Ready state

1. var sched = Scheduler new

2. sched block task

3. sched unblock task
   - Expected: is_ready is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

# Block then unblock
sched.block_task(id, BlockReason.Sleep(until_ns: 1000))
sched.unblock_task(id)

val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
```

</details>

#### unblock ignores tasks that are already runnable

1. var sched = Scheduler new

2. sched unblock task
   - Expected: sched.cpu_runnable_count(0u32) equals `before`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val before = sched.cpu_runnable_count(0u32)

sched.unblock_task(id)

expect(sched.cpu_runnable_count(0u32)).to_equal(before)
```

</details>

#### blocked task is not scheduled

1. var sched = Scheduler new

2. sched block task
   - Expected: current.id equals `id2.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id1 = sched.create_task(0x1000, TaskPriority.High, CapabilitySet.full())
val id2 = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())

# Block the high priority task
sched.block_task(id1, BlockReason.IpcRecv(port: 5))

# Schedule should pick Normal since High is blocked
val ctx = sched.schedule()
val current = sched.get_current()
expect(current.id).to_equal(id2.id)
```

</details>

#### wake_expired_sleepers unblocks only expired sleep deadlines

1. var sched = Scheduler new

2. sched block task
   - Expected: sched.wake_expired_sleepers(10000000) equals `0u32`

3. var tcb = sched get task

4. TaskState Blocked
   - Expected: is_blocked is true
   - Expected: sched.wake_expired_sleepers(20000000) equals `1u32`

5. tcb = sched get task
   - Expected: is_ready is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

sched.block_task(id, BlockReason.Sleep(until_ns: 20000000))
expect(sched.wake_expired_sleepers(10000000)).to_equal(0u32)

var tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_blocked = match task.state:
        TaskState.Blocked(reason): true
        _: false
    expect(is_blocked).to_equal(true)

expect(sched.wake_expired_sleepers(20000000)).to_equal(1u32)
tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
```

</details>

#### wake_expired_sleepers clears stale notification waiters

1. var sched = Scheduler new

2. notification register multi waiter

3. sched block task
   - Expected: sched.wake_expired_sleepers(10000000) equals `1u32`
   - Expected: notification_signal(g_notification_table, notif, 1u64) equals `0u64`
   - Expected: notification_poll(g_notification_table, notif) equals `1u64`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val notif = notification_create(g_notification_table)
val ids = [notif]
notification_register_multi_waiter(g_notification_table, ids, 1u64, id.id)

sched.block_task(id, BlockReason.Sleep(until_ns: 10000000))
expect(sched.wake_expired_sleepers(10000000)).to_equal(1u32)

expect(notification_signal(g_notification_table, notif, 1u64)).to_equal(0u64)
expect(notification_poll(g_notification_table, notif)).to_equal(1u64)
```

</details>

#### notification_signal stages every waiter registered on the same notification

<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = notification_create(g_notification_table)

expect(notification_wait(g_notification_table, notif, 101u64)).to_equal(0u64)
expect(notification_wait(g_notification_table, notif, 202u64)).to_equal(0u64)

expect(notification_signal(g_notification_table, notif, 1u64)).to_equal(101u64)

val staged = notification_drain_signaled_waiters(g_notification_table, notif)
expect(staged.len()).to_equal(2)
expect(staged[0]).to_equal(101u64)
expect(staged[1]).to_equal(202u64)
expect(notification_drain_signaled_waiters(g_notification_table, notif).len()).to_equal(0)
```

</details>

#### notification_clear_waiter removes staged waiters from future drains

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = notification_create(g_notification_table)

expect(notification_wait(g_notification_table, notif, 301u64)).to_equal(0u64)
expect(notification_wait(g_notification_table, notif, 302u64)).to_equal(0u64)

expect(notification_signal(g_notification_table, notif, 1u64)).to_equal(301u64)
expect(notification_clear_waiter(g_notification_table, 302u64)).to_equal(1u32)

val staged = notification_drain_signaled_waiters(g_notification_table, notif)
expect(staged.len()).to_equal(1)
expect(staged[0]).to_equal(301u64)
```

</details>

### exit_task

#### sets current task to Zombie state

1. var sched = Scheduler new

2. sched schedule

3. sched exit task
   - Expected: is_zombie is true
   - Expected: task.exit_code equals `42`


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())

# Schedule the task to make it current
sched.schedule()

# Exit with code 42
sched.exit_task(42)

val tcb = sched.get_task(id)
if tcb != nil:
    val task = tcb
    val is_zombie = match task.state:
        TaskState.Zombie: true
        _: false
    expect(is_zombie).to_equal(true)
    expect(task.exit_code).to_equal(42)
```

</details>

### fork and wait

#### clone_task creates a ready child with parent linkage

1. var sched = Scheduler new
   - Expected: is_ready is true
   - Expected: p.id equals `parent.id`


<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val parent = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val child = sched.clone_task(parent)

expect(child.id).to_be_greater_than(0)
val child_tcb = sched.get_task(child)
if child_tcb != nil:
    val task = child_tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
    if task.parent != nil:
        val p = task.parent.unwrap()
        expect(p.id).to_equal(parent.id)
```

</details>

#### clone_task prepares child fork return register as zero

1. var sched = Scheduler new

2. sched schedule

3. sched timer tick
   - Expected: task.context.rax equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val parent = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
sched.schedule()
val parent_ctx = TaskContext(
    rax: 123, rbx: 0, rcx: 0, rdx: 0,
    rsi: 0, rdi: 0, rbp: 0, rsp: 0,
    r8: 0, r9: 0, r10: 0, r11: 0,
    r12: 0, r13: 0, r14: 0, r15: 0,
    rip: 0x1000,
    rflags: 0x202,
    cs: 0x23,
    ss: 0x1B,
    fpu_state: 0
)
sched.timer_tick(parent_ctx)
val child = sched.clone_task(parent)

val child_tcb = sched.get_task(child)
if child_tcb != nil:
    val task = child_tcb
    expect(task.context.rax).to_equal(0)
```

</details>

#### wait_for rejects tasks that are not children

1. var sched = Scheduler new
   - Expected: status equals `-10`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val parent = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val unrelated = sched.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())

val status = sched.wait_for(parent, unrelated)

expect(status).to_equal(-10)
```

</details>

#### wait_for blocks parent while child is still live

1. var sched = Scheduler new
   - Expected: status equals `-11`

2. TaskState Blocked
   - Expected: is_blocked is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val parent = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val child = sched.clone_task(parent)

val status = sched.wait_for(parent, child)

expect(status).to_equal(-11)
val parent_tcb = sched.get_task(parent)
if parent_tcb != nil:
    val task = parent_tcb
    val is_blocked = match task.state:
        TaskState.Blocked(reason): true
        _: false
    expect(is_blocked).to_equal(true)
```

</details>

#### exit_task_by_id wakes a parent blocked in wait_for

1. var sched = Scheduler new
   - Expected: sched.wait_for(parent, child) equals `-11`

2. sched exit task by id
   - Expected: is_ready is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val parent = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val child = sched.clone_task(parent)

expect(sched.wait_for(parent, child)).to_equal(-11)
sched.exit_task_by_id(child, 5)

val parent_tcb = sched.get_task(parent)
if parent_tcb != nil:
    val task = parent_tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
```

</details>

#### wait_for collects zombie child exit status and frees the slot

1. var sched = Scheduler new

2. fd table init

3. pipe init

4. fd activate task
   - Expected: posix_pipe(unsafe_addr_of(read_fd), unsafe_addr_of(write_fd)) equals `0`
   - Expected: fd_set_status_flags(read_fd, O_RDONLY | O_NONBLOCK) equals `0`
   - Expected: fd_prepare_fork_to_task(child.id) equals `5u32`
   - Expected: pipe_close_write(write_fd) equals `0`

5. sched exit task by id
   - Expected: result.error equals `0`
   - Expected: result.pid equals `child.id`
   - Expected: result.status equals `7`
   - Expected: pipe_read(read_fd, unsafe_addr_of(buf), 1u64) equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val parent = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
fd_table_init()
pipe_init()
fd_activate_task(parent.id)

var read_fd: i32 = 0
var write_fd: i32 = 0
expect(posix_pipe(unsafe_addr_of(read_fd), unsafe_addr_of(write_fd))).to_equal(0)
expect(fd_set_status_flags(read_fd, O_RDONLY | O_NONBLOCK)).to_equal(0)

val child = sched.clone_task(parent)
expect(fd_prepare_fork_to_task(child.id)).to_equal(5u32)
expect(pipe_close_write(write_fd)).to_equal(0)
sched.exit_task_by_id(child, 7)

val result = sched.wait_for_collect(parent, child, true)

expect(result.error).to_equal(0)
expect(result.pid).to_equal(child.id)
expect(result.status).to_equal(7)
expect(sched.get_task(child)).to_be_nil

var buf: [u8; 1] = [0; 1]
expect(pipe_read(read_fd, unsafe_addr_of(buf), 1u64)).to_equal(0)
```

</details>

### get_task

#### returns nil for non-existent task

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sched = Scheduler.new()
val result = sched.get_task(TaskId(id: 999))
expect(result).to_be_nil
```

</details>

#### returns the task for valid id

1. var sched = Scheduler new
   - Expected: found is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sched = Scheduler.new()
val id = sched.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = sched.get_task(id)
val found = result != nil
expect(found).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 69 |
| Active scenarios | 69 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
