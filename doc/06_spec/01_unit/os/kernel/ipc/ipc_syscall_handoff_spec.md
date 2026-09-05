# IPC Syscall Handoff Specification

> This unit spec proves the SimpleOS IPC syscall handoff path used by user-mode syscalls and scheduler wakeups. A blocking receive must stage the current task as a port waiter, and a send to that port must unblock and consume exactly one waiting receiver.

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

# IPC Syscall Handoff Specification

This unit spec proves the SimpleOS IPC syscall handoff path used by user-mode syscalls and scheduler wakeups. A blocking receive must stage the current task as a port waiter, and a send to that port must unblock and consume exactly one waiting receiver.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #simpleos-ipc-syscall-handoff |
| Category | SimpleOS / IPC / Scheduler |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/multicore_green.md |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | doc/05_design/multicore_green.md |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This unit spec proves the SimpleOS IPC syscall handoff path used by user-mode
syscalls and scheduler wakeups. A blocking receive must stage the current task
as a port waiter, and a send to that port must unblock and consume exactly one
waiting receiver.

## Requirements

**Requirements:** doc/02_requirements/feature/multicore_green.md

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** doc/05_design/multicore_green.md

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the IPC handoff proof:

```sh
src/compiler_rust/target/debug/simple test test/01_unit/os/kernel/ipc/ipc_syscall_handoff_spec.spl --mode=interpreter --clean
```

## Examples

The send scenario covers the regression where the IPC syscall wrapper reached
the scheduler unblock path but did not complete the waiter-consumption handoff
under the interpreter. It now calls the explicit CPU-aware unblock path and
verifies the port waiter list is empty after the send.

## Scenarios

### IPC syscall handoff

#### blocking recv records the current task as a port waiter

- Create a scheduler, IPC manager, and receiver-owned port
- var scheduler = Scheduler new
- var ipc = IpcManager new
- Invoke blocking IPC receive on an empty port
- Verify the current task is staged as the port waiter
   - Expected: state.result.value equals `0`
   - Expected: has_waiter is true
   - Expected: task_id.id equals `receiver.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a scheduler, IPC manager, and receiver-owned port")
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = scheduler.get_current()
val port = ipc.create_port(receiver, "ipc_blocking_recv")

step("Invoke blocking IPC receive on an empty port")
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

step("Verify the current task is staged as the port waiter")
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

- Create a scheduler, IPC manager, and a waiting receiver
- var scheduler = Scheduler new
- var ipc = IpcManager new
- ipc add waiter
- Send a message to the receiver-owned port
- Verify the send succeeds and consumes exactly one waiter
   - Expected: state.result.value equals `0`
   - Expected: state.ipc.get_first_waiter(port.id) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a scheduler, IPC manager, and a waiting receiver")
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val receiver = TaskId(id: 99)
val port = ipc.create_port(receiver, "ipc_send_wake")
ipc.add_waiter(port, receiver)

step("Send a message to the receiver-owned port")
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

step("Verify the send succeeds and consumes exactly one waiter")
expect(state.result.value).to_equal(0)
expect(state.ipc.get_first_waiter(port.id) == nil).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/multicore_green.md](doc/02_requirements/feature/multicore_green.md)
- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Design:** [doc/05_design/multicore_green.md](doc/05_design/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
