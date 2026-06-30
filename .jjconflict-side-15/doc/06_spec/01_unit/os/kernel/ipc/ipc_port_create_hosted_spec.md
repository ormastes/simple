# Ipc Port Create Hosted Specification

> 1. var mgr = IpcManager new

<!-- sdn-diagram:id=ipc_port_create_hosted_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_port_create_hosted_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_port_create_hosted_spec -> std
ipc_port_create_hosted_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_port_create_hosted_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Port Create Hosted Specification

## Scenarios

### IpcManager.create_port (hosted)

#### returns a port with a positive id

1. var mgr = IpcManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 7)
val port = mgr.create_port(owner, "compositor")
expect(port.id).to_be_greater_than(0)
```

</details>

#### stores the owner task id on the created port

1. var mgr = IpcManager new
   - Expected: port.owner equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 42)
val port = mgr.create_port(owner, "compositor")
expect(port.owner).to_equal(42)
```

</details>

#### assigns distinct ids to successive ports

1. var mgr = IpcManager new
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val p1 = mgr.create_port(owner, "compositor")
val p2 = mgr.create_port(owner, "launcher")
val different = p1.id != p2.id
expect(different).to_equal(true)
```

</details>

#### allows connect-by-name after create

1. var mgr = IpcManager new
2. mgr create port
   - Expected: found_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 3)
mgr.create_port(owner, "compositor")
val found = mgr.connect("compositor")
val found_ok = found != nil
expect(found_ok).to_equal(true)
```

</details>

### syscall_handler id=22 SYS_IPC_CREATE_PORT (hosted)

#### dispatches to _handle_ipc_create_port and returns positive id

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: is_enosys is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(
        id: 22,
        arg0: 0,
        arg1: 0,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
# Hosted path must NOT return -38; it must return a valid port id.
val is_enosys = result.value == -38
expect(is_enosys).to_equal(false)
expect(result.value).to_be_greater_than(0)
```

</details>

#### returns monotonically increasing ids on repeated calls

1. var scheduler = Scheduler new
2. var ipc = IpcManager new
3. SyscallArgs
4. SyscallArgs
   - Expected: growing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
var ipc = IpcManager.new()
val klog = KernelLog.new(16)
val a = syscall_handler(
    SyscallArgs(id: 22, arg0: 0, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    scheduler, ipc, klog
)
val b = syscall_handler(
    SyscallArgs(id: 22, arg0: 0, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    scheduler, ipc, klog
)
expect(a.value).to_be_greater_than(0)
expect(b.value).to_be_greater_than(0)
val growing = b.value > a.value
expect(growing).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/ipc_port_create_hosted_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IpcManager.create_port (hosted)
- syscall_handler id=22 SYS_IPC_CREATE_PORT (hosted)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
