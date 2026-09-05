# Riscv64 Syscall Ipc Specification

> <details>

<!-- sdn-diagram:id=riscv64_syscall_ipc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_syscall_ipc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_syscall_ipc_spec -> std
riscv64_syscall_ipc_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_syscall_ipc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Syscall Ipc Specification

## Scenarios

### RV64 arch-local IPC syscalls

#### create/connect preserves IPC state without the common syscall stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
val ipc = IpcManager.new()
val created = rv64_syscall_handler_state(rv64_args(22, 0, 0, 0, 0), scheduler, ipc, KernelLog.new(8))
expect(created.result.value).to_be_greater_than(0)

val connected = rv64_syscall_handler_state(rv64_args(23, 0, 0, 0, 0), created.scheduler, created.ipc, KernelLog.new(8))
expect(connected.result.value).to_equal(created.result.value)
```

</details>

#### send/recv delivers one message through returned IPC state

1. var ipc = IpcManager new
   - Expected: sent.result.value equals `0`
   - Expected: received.result.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scheduler = Scheduler.new()
var ipc = IpcManager.new()
val port = ipc.create_port(TaskId(id: 0), "rv64_ipc")

val sent = rv64_syscall_handler_state(rv64_args(20, port.id, 7, 0, 0), scheduler, ipc, KernelLog.new(8))
expect(sent.result.value).to_equal(0)

val received = rv64_syscall_handler_state(rv64_args(21, port.id, 0, 0, 0), sent.scheduler, sent.ipc, KernelLog.new(8))
expect(received.result.value).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64_syscall_ipc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RV64 arch-local IPC syscalls

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
