# IPC Manager Specification

> Tests for the kernel IPC manager. Validates port lifecycle (create, connect), message passing (send, recv), and capability delegation (grant, check, revoke) through the IPC subsystem.

<!-- sdn-diagram:id=ipc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_spec -> std
ipc_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# IPC Manager Specification

Tests for the kernel IPC manager. Validates port lifecycle (create, connect), message passing (send, recv), and capability delegation (grant, check, revoke) through the IPC subsystem.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-006 |
| Category | Runtime |
| Difficulty | 4/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/os/kernel/ipc/ipc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the kernel IPC manager. Validates port lifecycle (create, connect),
message passing (send, recv), and capability delegation (grant, check, revoke)
through the IPC subsystem.

## Scenarios

### IpcManager

### construction

#### creates with empty port table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mgr = IpcManager.new()
# Connecting to a non-existent port returns nil
val port = mgr.connect("nonexistent")
expect(port == nil).to_equal(true)
```

</details>

### create_port

#### returns a port with non-zero id

1. var mgr = IpcManager new


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val port = mgr.create_port(owner, "test_port")
expect(port.id).to_be_greater_than(0)
```

</details>

#### assigns sequential port ids

1. var mgr = IpcManager new
   - Expected: p2.id equals `p1.id + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val p1 = mgr.create_port(owner, "port_a")
val p2 = mgr.create_port(owner, "port_b")
expect(p2.id).to_equal(p1.id + 1)
```

</details>

#### stores the owner task id

1. var mgr = IpcManager new
   - Expected: port.owner equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 42)
val port = mgr.create_port(owner, "my_port")
expect(port.owner).to_equal(42)
```

</details>

#### creates multiple ports for different tasks

1. var mgr = IpcManager new
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner1 = TaskId(id: 1)
val owner2 = TaskId(id: 2)
val p1 = mgr.create_port(owner1, "vfs")
val p2 = mgr.create_port(owner2, "compositor")
expect(p1.id).to_be_greater_than(0)
expect(p2.id).to_be_greater_than(0)
val different = p1.id != p2.id
expect(different).to_equal(true)
```

</details>

### connect

#### finds existing port by name

1. var mgr = IpcManager new
   - Expected: found_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val created = mgr.create_port(owner, "vfs_service")
val found = mgr.connect("vfs_service")
val found_ok = found != nil
expect(found_ok).to_equal(true)
```

</details>

#### returns nil for non-existent port

1. var mgr = IpcManager new
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val result = mgr.connect("does_not_exist")
expect(result == nil).to_equal(true)
```

</details>

#### returns correct port id on connect

1. var mgr = IpcManager new
   - Expected: port.id equals `created.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 5)
val created = mgr.create_port(owner, "audio")
val found = mgr.connect("audio")
if found != nil:
    val port = found
    expect(port.id).to_equal(created.id)
```

</details>

#### distinguishes ports by name

1. var mgr = IpcManager new
   - Expected: port.id equals `p1.id`
   - Expected: port.id equals `p2.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val p1 = mgr.create_port(owner, "service_a")
val p2 = mgr.create_port(owner, "service_b")
val found_a = mgr.connect("service_a")
val found_b = mgr.connect("service_b")
if found_a != nil:
    val port = found_a
    expect(port.id).to_equal(p1.id)
if found_b != nil:
    val port = found_b
    expect(port.id).to_equal(p2.id)
```

</details>

### IpcManager message passing

### send

#### returns 0 on successful send

1. var mgr = IpcManager new
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val port = mgr.create_port(owner, "inbox")
val msg = IpcMessage(
    src_port: 0,
    dst_port: port.id,
    method: 1,
    flags: 0,
    payload_len: 0,
    cap_count: 0
)
val result = mgr.send(msg)
expect(result).to_equal(0)
```

</details>

#### returns -1 for non-existent destination

1. var mgr = IpcManager new
   - Expected: result equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val msg = IpcMessage(
    src_port: 0,
    dst_port: 9999,
    method: 1,
    flags: 0,
    payload_len: 0,
    cap_count: 0
)
val result = mgr.send(msg)
expect(result).to_equal(-1)
```

</details>

#### preserves a waiting receiver for the syscall unblock handoff

1. var mgr = IpcManager new
2. mgr add waiter
   - Expected: result equals `0`
   - Expected: has_waiter is true
   - Expected: task.id equals `waiter.id`
   - Expected: mgr.get_first_waiter(port.id) == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val waiter = TaskId(id: 99)
val port = mgr.create_port(owner, "waiter_handoff")
mgr.add_waiter(port, waiter)
val msg = IpcMessage(
    src_port: 0,
    dst_port: port.id,
    method: 7,
    flags: 0,
    payload_len: 0,
    cap_count: 0
)

val result = mgr.send(msg)
val first = mgr.get_first_waiter(port.id)

expect(result).to_equal(0)
val has_waiter = first != nil
expect(has_waiter).to_equal(true)
if first != nil:
    val task = first
    expect(task.id).to_equal(waiter.id)
expect(mgr.get_first_waiter(port.id) == nil).to_equal(true)
```

</details>

### recv

#### returns nil for empty port (non-blocking)

1. var mgr = IpcManager new
   - Expected: msg == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val port = mgr.create_port(owner, "empty_port")
val msg = mgr.recv(port, 0)
expect(msg == nil).to_equal(true)
```

</details>

#### returns sent message

1. var mgr = IpcManager new
2. mgr send
   - Expected: got_msg is true
   - Expected: msg.method equals `42`
   - Expected: msg.src_port equals `100`
   - Expected: msg.payload_len equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val port = mgr.create_port(owner, "recv_test")

# Send a message
val outgoing = IpcMessage(
    src_port: 100,
    dst_port: port.id,
    method: 42,
    flags: 0,
    payload_len: 128,
    cap_count: 0
)
mgr.send(outgoing)

# Receive it
val received = mgr.recv(port, 0)
val got_msg = received != nil
expect(got_msg).to_equal(true)
if received != nil:
    val msg = received
    expect(msg.method).to_equal(42)
    expect(msg.src_port).to_equal(100)
    expect(msg.payload_len).to_equal(128)
```

</details>

#### delivers messages in FIFO order

1. var mgr = IpcManager new
2. mgr send
3. mgr send
   - Expected: m.method equals `10`
   - Expected: m.method equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val port = mgr.create_port(owner, "fifo_test")

# Send two messages with different methods
val msg1 = IpcMessage(
    src_port: 1, dst_port: port.id,
    method: 10, flags: 0, payload_len: 0, cap_count: 0
)
val msg2 = IpcMessage(
    src_port: 2, dst_port: port.id,
    method: 20, flags: 0, payload_len: 0, cap_count: 0
)
mgr.send(msg1)
mgr.send(msg2)

# First recv should get method=10
val first = mgr.recv(port, 0)
if first != nil:
    val m = first
    expect(m.method).to_equal(10)

# Second recv should get method=20
val second = mgr.recv(port, 0)
if second != nil:
    val m = second
    expect(m.method).to_equal(20)
```

</details>

#### returns nil after all messages consumed

1. var mgr = IpcManager new
2. mgr send
3. mgr recv
   - Expected: empty == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val owner = TaskId(id: 1)
val port = mgr.create_port(owner, "exhaust_test")

val msg = IpcMessage(
    src_port: 1, dst_port: port.id,
    method: 1, flags: 0, payload_len: 0, cap_count: 0
)
mgr.send(msg)
mgr.recv(port, 0)  # Consume the message
val empty = mgr.recv(port, 0)
expect(empty == nil).to_equal(true)
```

</details>

### IpcManager capability delegation

### cap_check

#### returns false for task without capabilities

1. var mgr = IpcManager new
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val task = TaskId(id: 1)
val result = mgr.cap_check(task, CapabilityKind.ProcessSpawn)
expect(result).to_equal(false)
```

</details>

### cap_grant and cap_check

#### grants capability from one task to another

1. var mgr = IpcManager new
2. mgr cap manager init task
3. mgr cap manager init task
   - Expected: ok is true
   - Expected: has_cap is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val from_task = TaskId(id: 1)
val to_task = TaskId(id: 2)

# Initialize source task with a capability
val token = CapabilityToken(
    kind: CapabilityKind.ProcessSpawn,
    generation: 1,
    owner: from_task.id
)
val caps = CapabilitySet(caps: [token], is_pledged: false)
mgr.cap_manager.init_task(from_task, caps)
mgr.cap_manager.init_task(to_task, CapabilitySet.full())

# Grant from source to target
val ok = mgr.cap_grant(from_task, to_task, token)
expect(ok).to_equal(true)

# Target should now have the capability
val has_cap = mgr.cap_check(to_task, CapabilityKind.ProcessSpawn)
expect(has_cap).to_equal(true)
```

</details>

### cap_revoke

#### revokes a granted capability

1. var mgr = IpcManager new
2. mgr cap manager init task
3. mgr cap manager init task
4. mgr cap grant
   - Expected: revoked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = IpcManager.new()
val task1 = TaskId(id: 1)
val task2 = TaskId(id: 2)

val token = CapabilityToken(
    kind: CapabilityKind.SystemReboot,
    generation: 1,
    owner: task1.id
)
val caps = CapabilitySet(caps: [token], is_pledged: false)
mgr.cap_manager.init_task(task1, caps)
mgr.cap_manager.init_task(task2, CapabilitySet.full())

# Grant then revoke
mgr.cap_grant(task1, task2, token)
val revoked = mgr.cap_revoke(token)
expect(revoked).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
