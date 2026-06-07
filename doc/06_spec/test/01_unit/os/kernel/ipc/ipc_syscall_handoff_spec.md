# Ipc Syscall Handoff Specification

> 1. var scheduler = Scheduler new

<!-- sdn-diagram:id=ipc_syscall_handoff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_syscall_handoff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_syscall_handoff_spec -> std
ipc_syscall_handoff_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_syscall_handoff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Syscall Handoff Specification

## Scenarios

### IPC syscall handoff

#### blocking recv records the current task as a port waiter

1. var scheduler = Scheduler new
2. var ipc = IpcManager new
   - Expected: state.result.value equals `0`
   - Expected: has_waiter is true
   - Expected: task_id.id equals `receiver.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = scheduler.get_current()
val port = ipc.create_port(receiver, "ipc_blocking_recv")

val state = _handle_ipc_recv_state(
    SyscallArgs(
        id: 21,
        arg0: port.id,
        arg1: 1,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    ipc
)

expect(state.result.value).to_equal(0)
val waiter = state.ipc.get_first_waiter(port.id)
val has_waiter = waiter != nil
expect(has_waiter).to_equal(true)
if waiter != nil:
    val task_id = waiter
    expect(task_id.id).to_equal(receiver.id)
```

</details>

#### send unblocks the first waiting receiver and consumes one waiter

1. var scheduler = Scheduler new
2. var ipc = IpcManager new
3. ipc add waiter
   - Expected: state.result.value equals `0`
   - Expected: state.ipc.get_first_waiter(port.id) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = TaskId(id: 99)
val port = ipc.create_port(receiver, "ipc_send_wake")
ipc.add_waiter(port, receiver)

val state = _handle_ipc_send_state(
    SyscallArgs(
        id: 20,
        arg0: port.id,
        arg1: 7,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    ipc
)

expect(state.result.value).to_equal(0)
expect(state.ipc.get_first_waiter(port.id) == nil).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPC syscall handoff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
