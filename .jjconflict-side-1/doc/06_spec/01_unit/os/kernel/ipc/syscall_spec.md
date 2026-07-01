# syscall_spec

> Syscall dispatcher tests for process launch and scheduler control paths.

<!-- sdn-diagram:id=syscall_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_spec -> std
syscall_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 47 | 47 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# syscall_spec

Syscall dispatcher tests for process launch and scheduler control paths.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/syscall_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Syscall dispatcher tests for process launch and scheduler control paths.

## Scenarios

### syscall_handler

#### copies active task ids and task info for process diagnostics

1. var scheduler = Scheduler new
   - Expected: _map_user_pollfd_page(pid_buf) is true
2. IpcManager new
3. KernelLog new
   - Expected: list_result.value equals `2`
   - Expected: mmio_read64(pid_buf) equals `first.id`
   - Expected: mmio_read64(pid_buf + 8) equals `second.id`
4. IpcManager new
5. KernelLog new
   - Expected: info_result.value equals `0`
   - Expected: mmio_read64(info_buf) equals `second.id`
   - Expected: mmio_read64(info_buf + 8) equals `0`
   - Expected: mmio_read8(info_buf + 16) equals `0u8`
   - Expected: mmio_read8(info_buf + 17) equals `3u8`
   - Expected: mmio_read32(info_buf + 40) equals `6u32`
   - Expected: mmio_read8(name_buf) equals `116u8`
   - Expected: mmio_read8(name_buf + 5) equals `50u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val first = scheduler.create_task(0x1000, TaskPriority.High, CapabilitySet.full())
val second = scheduler.create_task(0x2000, TaskPriority.Low, CapabilitySet.full())
val pid_buf = 0x12000000u64
val info_buf = 0x12000100u64
val name_buf = 0x12000200u64
expect(_map_user_pollfd_page(pid_buf)).to_equal(true)

val list_result = syscall_handler(
    SyscallArgs(
        id: 5,
        arg0: pid_buf,
        arg1: 4,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(list_result.value).to_equal(2)
expect(mmio_read64(pid_buf)).to_equal(first.id)
expect(mmio_read64(pid_buf + 8)).to_equal(second.id)

val info_result = syscall_handler(
    SyscallArgs(
        id: 6,
        arg0: second.id,
        arg1: info_buf,
        arg2: name_buf,
        arg3: 64,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(info_result.value).to_equal(0)
expect(mmio_read64(info_buf)).to_equal(second.id)
expect(mmio_read64(info_buf + 8)).to_equal(0)
expect(mmio_read8(info_buf + 16)).to_equal(0u8)
expect(mmio_read8(info_buf + 17)).to_equal(3u8)
expect(mmio_read32(info_buf + 40)).to_equal(6u32)
expect(mmio_read8(name_buf)).to_equal(116u8)
expect(mmio_read8(name_buf + 5)).to_equal(50u8)
```

</details>

#### launches built-in service binaries through spawn_binary

1. var scheduler = Scheduler new
2. arg1: path len
3. IpcManager new
4. KernelLog new
   - Expected: found equals `1`
   - Expected: task.is_user is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/services/vfs"
var scheduler = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_be_greater_than(0)
val spawned = scheduler.get_task(TaskId(id: result.value as u64))
val found = if spawned == nil: 0 else: 1
expect(found).to_equal(1)
if spawned != nil:
    val task = spawned
    expect(task.is_user).to_equal(true)
```

</details>

#### sleep syscall blocks current task on a scheduler deadline

1. var scheduler = Scheduler new
2. scheduler schedule
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `0`
5. TaskState Blocked
6. BlockReason Sleep
   - Expected: blocked_until equals `20000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task_id = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()

val result = syscall_handler(
    SyscallArgs(
        id: 51,
        arg0: 15000000,
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

expect(result.value).to_equal(0)
val tcb = scheduler.get_task(task_id)
if tcb != nil:
    val task = tcb
    val blocked_until = match task.state:
        TaskState.Blocked(reason):
            match reason:
                BlockReason.Sleep(until_ns): until_ns
                _: 0u64
        _: 0u64
    expect(blocked_until).to_equal(20000000u64)
```

</details>

#### dispatch marks blocking sleep as BlockCurrent

1. var scheduler = Scheduler new
2. scheduler create task
3. scheduler schedule
4. IpcManager new
5. KernelLog new
   - Expected: result.result.value equals `0`
   - Expected: result.disposition equals `SyscallTrapDisposition.BlockCurrent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()

val result = syscall_dispatch(
    SyscallArgs(
        id: 51,
        arg0: 15000000,
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

expect(result.result.value).to_equal(0)
expect(result.disposition).to_equal(SyscallTrapDisposition.BlockCurrent)
```

</details>

#### poll with no fds and finite timeout blocks on a scheduler deadline

1. var scheduler = Scheduler new
2. scheduler schedule
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `0`
5. TaskState Blocked
6. BlockReason Sleep
   - Expected: blocked_until equals `30000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task_id = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()

val result = syscall_handler(
    SyscallArgs(
        id: 68,
        arg0: 0,
        arg1: 0,
        arg2: 25,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(0)
val tcb = scheduler.get_task(task_id)
if tcb != nil:
    val task = tcb
    val blocked_until = match task.state:
        TaskState.Blocked(reason):
            match reason:
                BlockReason.Sleep(until_ns): until_ns
                _: 0u64
        _: 0u64
    expect(blocked_until).to_equal(30000000u64)
```

</details>

#### dispatch marks blocking poll as BlockCurrent

1. var scheduler = Scheduler new
2. scheduler create task
3. scheduler schedule
4. IpcManager new
5. KernelLog new
   - Expected: result.result.value equals `0`
   - Expected: result.disposition equals `SyscallTrapDisposition.BlockCurrent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()

val result = syscall_dispatch(
    SyscallArgs(
        id: 68,
        arg0: 0,
        arg1: 0,
        arg2: 25,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.result.value).to_equal(0)
expect(result.disposition).to_equal(SyscallTrapDisposition.BlockCurrent)
```

</details>

#### poll treats any negative timeout as an infinite wait

1. var scheduler = Scheduler new
2. scheduler schedule
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `0`
5. TaskState Blocked
6. BlockReason Sleep
   - Expected: blocked_until equals `0xFFFFFFFFFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task_id = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()

val result = syscall_handler(
    SyscallArgs(
        id: 68,
        arg0: 0,
        arg1: 0,
        arg2: 0xFFFFFFFFFFFFFFFE,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(0)
val tcb = scheduler.get_task(task_id)
if tcb != nil:
    val task = tcb
    val blocked_until = match task.state:
        TaskState.Blocked(reason):
            match reason:
                BlockReason.Sleep(until_ns): until_ns
                _: 0u64
        _: 0u64
    expect(blocked_until).to_equal(0xFFFFFFFFFFFFFFFF)
```

</details>

#### poll returns -EINVAL when more than four notification-backed fds are passed

1. fd table init
   - Expected: _map_user_pollfd_page(pollfds_ptr) is true
2. fd set
   - Expected: fd_set_poll_notification(fd, POLLIN, notif) equals `0`
3.  write pollfd
4. var scheduler = Scheduler new
5. scheduler schedule
6. IpcManager new
7. KernelLog new
   - Expected: result.value equals `-22`
8. TaskState Blocked
   - Expected: is_blocked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
val pollfds_ptr = 0x10000000u64
expect(_map_user_pollfd_page(pollfds_ptr)).to_equal(true)

var i: u64 = 0
while i < 5:
    val fd = (3 + i) as i32
    val notif = notification_create(g_notification_table)
    fd_set(fd, FD_TYPE_PIPE_READ, O_RDONLY, (10 + i) as u64)
    expect(fd_set_poll_notification(fd, POLLIN, notif)).to_equal(0)
    _write_pollfd(pollfds_ptr, i, fd, POLLIN)
    i = i + 1

var scheduler = Scheduler.new()
val task_id = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()

val result = syscall_handler(
    SyscallArgs(
        id: 68,
        arg0: pollfds_ptr,
        arg1: 5,
        arg2: 25,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(-22)
val tcb = scheduler.get_task(task_id)
if tcb != nil:
    val task = tcb
    val is_blocked = match task.state:
        TaskState.Blocked(reason): true
        _: false
    expect(is_blocked).to_equal(false)
```

</details>

#### poll with a notification-backed fd and finite timeout blocks on a scheduler deadline

1. fd table init
   - Expected: _map_user_pollfd_page(pollfds_ptr) is true
2. fd set
   - Expected: fd_set_poll_notification(fd, POLLIN, notif) equals `0`
3.  write pollfd
4. var scheduler = Scheduler new
5. scheduler schedule
6. IpcManager new
7. KernelLog new
   - Expected: result.value equals `0`
8. TaskState Blocked
9. BlockReason Sleep
   - Expected: blocked_until equals `30000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
val pollfds_ptr = 0x10000000u64
expect(_map_user_pollfd_page(pollfds_ptr)).to_equal(true)

val fd = 3
val notif = notification_create(g_notification_table)
fd_set(fd, FD_TYPE_PIPE_READ, O_RDONLY, 10u64)
expect(fd_set_poll_notification(fd, POLLIN, notif)).to_equal(0)
_write_pollfd(pollfds_ptr, 0, fd, POLLIN)

var scheduler = Scheduler.new()
val task_id = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()

val result = syscall_handler(
    SyscallArgs(
        id: 68,
        arg0: pollfds_ptr,
        arg1: 1,
        arg2: 25,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(0)
val tcb = scheduler.get_task(task_id)
if tcb != nil:
    val task = tcb
    val blocked_until = match task.state:
        TaskState.Blocked(reason):
            match reason:
                BlockReason.Sleep(until_ns): until_ns
                _: 0u64
        _: 0u64
    expect(blocked_until).to_equal(30000000u64)
```

</details>

#### notification signal syscall wakes every staged waiter

1. var scheduler = Scheduler new
   - Expected: notification_wait(g_notification_table, notif, first.id) equals `0u64`
   - Expected: notification_wait(g_notification_table, notif, second.id) equals `0u64`
2. scheduler block task
3. scheduler block task
4. IpcManager new
5. KernelLog new
   - Expected: result.value equals `0`
   - Expected: is_ready is true
   - Expected: is_ready is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val first = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val second = scheduler.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
val notif = notification_create(g_notification_table)
expect(notification_wait(g_notification_table, notif, first.id)).to_equal(0u64)
expect(notification_wait(g_notification_table, notif, second.id)).to_equal(0u64)
scheduler.block_task(first, BlockReason.Notification(id: notif))
scheduler.block_task(second, BlockReason.Notification(id: notif))

val result = syscall_handler(
    SyscallArgs(
        id: 25,
        arg0: notif,
        arg1: 1,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(0)
val first_tcb = scheduler.get_task(first)
val second_tcb = scheduler.get_task(second)
if first_tcb != nil:
    val task = first_tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
if second_tcb != nil:
    val task = second_tcb
    val is_ready = match task.state:
        TaskState.Ready: true
        _: false
    expect(is_ready).to_equal(true)
```

</details>

#### launches the canonical rv64 proof binary path through spawn_binary

1. var scheduler = Scheduler new
2. arg1: path len
3. IpcManager new
4. KernelLog new
   - Expected: found equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = RV64_PROOF_BINARY_PATH
var scheduler = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_be_greater_than(0)
val spawned = scheduler.get_task(TaskId(id: result.value as u64))
val found = if spawned == nil: 0 else: 1
expect(found).to_equal(1)
```

</details>

#### rejects missing executable bytes without resident fallback

1. var scheduler = Scheduler new
2. arg1: path len
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/apps/hello_world"
var scheduler = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(-2)
val spawned = scheduler.get_task(TaskId(id: 1))
expect(spawned).to_be_nil()
```

</details>

#### direct sentinel spawn creates process-backed user task for valid filesystem ELF

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. var scheduler = Scheduler new
   - Expected: found equals `1`
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x400000`
4.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world", _make_x86_64_exec())
var scheduler = Scheduler.new()
val pid = dispatch_spawn_binary_direct(3, 0, 2, scheduler, KernelLog.new(16))
expect(pid).to_be_greater_than(0)
expect(pid).not_to_equal(4103)
val spawned = scheduler.get_task(TaskId(id: pid as u64))
val found = if spawned == nil: 0 else: 1
expect(found).to_equal(1)
if spawned != nil:
    val task = spawned
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x400000)
_clear_synthetic_vfs_for_test()
```

</details>

#### architecture-param spawn handoff accepts x86_32 ELF images

1. var scheduler = Scheduler new
2.  make x86 32 exec
3. KernelLog new
   - Expected: found equals `1`
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x8048000`
   - Expected: task.user_stack equals `0x00000000BFFFF000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val pid = _spawn_from_resolved_bytes_for_arch(
    "/sys/apps/x86_32_probe",
    [],
    _make_x86_32_exec(),
    2,
    scheduler,
    KernelLog.new(16),
    Architecture.X86
)
expect(pid).to_be_greater_than(0)
val spawned = scheduler.get_task(TaskId(id: pid as u64))
val found = if spawned == nil: 0 else: 1
expect(found).to_equal(1)
if spawned != nil:
    val task = spawned
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x8048000)
    expect(task.user_stack).to_equal(0x00000000BFFFF000)
```

</details>

#### direct SMF sentinel spawn creates process-backed user task without resident fallback

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. var scheduler = Scheduler new
   - Expected: found equals `1`
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x400000`
4.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world.smf", _make_exec_smf(_make_x86_64_exec()))
var scheduler = Scheduler.new()
val pid = dispatch_spawn_binary_direct(103, 0, 2, scheduler, KernelLog.new(16))
expect(pid).to_be_greater_than(0)
expect(pid).not_to_equal(4103)
val spawned = scheduler.get_task(TaskId(id: pid as u64))
val found = if spawned == nil: 0 else: 1
expect(found).to_equal(1)
if spawned != nil:
    val task = spawned
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x400000)
_clear_synthetic_vfs_for_test()
```

</details>

#### spawn_binary creates process-backed user task for executable SMF package

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. var scheduler = Scheduler new
4. arg1: path len
5. IpcManager new
6. KernelLog new
   - Expected: found equals `1`
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x400000`
7.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
val path = "/home/RUNME.SMF"
_set_synthetic_vfs_file_for_test(path, _make_exec_smf(_make_x86_64_exec()))
var scheduler = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_be_greater_than(0)
val spawned = scheduler.get_task(TaskId(id: result.value as u64))
val found = if spawned == nil: 0 else: 1
expect(found).to_equal(1)
if spawned != nil:
    val task = spawned
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x400000)
_clear_synthetic_vfs_for_test()
```

</details>

#### spawn_binary enforces AI CLI process grants before executable resolution

1.  clear synthetic vfs for test
2. set ai cli process manifest for test
3.  set synthetic vfs file for test
4.  set synthetic vfs file for test
5. var allowed scheduler = Scheduler new
6. arg1: allowed path len
7. IpcManager new
8. KernelLog new
9. var denied scheduler = Scheduler new
10. arg1: denied path len
11. IpcManager new
12. KernelLog new
   - Expected: denied.value equals `-13`
13. clear ai cli process manifest for test
14.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
set_ai_cli_process_manifest_for_test(codex_cli_smoke_manifest())
val allowed_path = "/usr/bin/git"
val denied_path = "/bin/sh"
_set_synthetic_vfs_file_for_test(allowed_path, _make_x86_64_exec())
_set_synthetic_vfs_file_for_test(denied_path, _make_x86_64_exec())

var allowed_scheduler = Scheduler.new()
val allowed = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &allowed_path as u64,
        arg1: allowed_path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    allowed_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(allowed.value).to_be_greater_than(0)

var denied_scheduler = Scheduler.new()
val denied = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &denied_path as u64,
        arg1: denied_path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    denied_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(denied.value).to_equal(-13)
expect(denied_scheduler.get_task(TaskId(id: 1))).to_be_nil()

clear_ai_cli_process_manifest_for_test()
_clear_synthetic_vfs_for_test()
```

</details>

#### direct sentinel spawn enforces AI CLI process grants

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. set ai cli process manifest for test
4. var scheduler = Scheduler new
   - Expected: denied equals `-13`
5. clear ai cli process manifest for test
6.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world", _make_x86_64_exec())
set_ai_cli_process_manifest_for_test(codex_cli_smoke_manifest())

var scheduler = Scheduler.new()
val denied = dispatch_spawn_binary_direct(3, 0, 2, scheduler, KernelLog.new(16))
expect(denied).to_equal(-13)
expect(scheduler.get_task(TaskId(id: 1))).to_be_nil()

clear_ai_cli_process_manifest_for_test()
_clear_synthetic_vfs_for_test()
```

</details>

#### direct sentinel spawn rejects malformed filesystem bytes without resident fallback

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. var scheduler = Scheduler new
   - Expected: pid equals `-8`
4.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world", [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8])
var scheduler = Scheduler.new()
val pid = dispatch_spawn_binary_direct(3, 0, 2, scheduler, KernelLog.new(16))
expect(pid).to_equal(-8)
val spawned = scheduler.get_task(TaskId(id: 1))
expect(spawned).to_be_nil()
_clear_synthetic_vfs_for_test()
```

</details>

#### rejects unknown spawn_binary paths

1. arg1: path len
2. Scheduler new
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/apps/does_not_exist"
val result = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    Scheduler.new(),
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(-2)
```

</details>

#### rejects empty spawn_binary requests

1. Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: 0,
        arg1: 0,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    Scheduler.new(),
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(-22)
```

</details>

#### rejects oversized spawn_binary paths

1. arg1: path len
2. Scheduler new
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
val result = syscall_handler(
    SyscallArgs(
        id: 13,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 2,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    Scheduler.new(),
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(-22)
```

</details>

#### fork syscall clones the current scheduler task

1. var scheduler = Scheduler new
2. scheduler schedule
3. IpcManager new
4. KernelLog new
   - Expected: p.id equals `parent.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val result = syscall_handler(
    SyscallArgs(
        id: 57,
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
expect(result.value).to_be_greater_than(0)
val child = scheduler.get_task(TaskId(id: result.value as u64))
if child != nil:
    val task = child
    if task.parent != nil:
        val p = task.parent.unwrap()
        expect(p.id).to_equal(parent.id)
```

</details>

#### wait syscall blocks current parent while child is live

1. var scheduler = Scheduler new
2. scheduler schedule
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `0`
5. TaskState Blocked
   - Expected: is_blocked is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val child = scheduler.clone_task(parent)
val result = syscall_handler(
    SyscallArgs(
        id: 3,
        arg0: child.id,
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
expect(result.value).to_equal(0)
val parent_tcb = scheduler.get_task(parent)
if parent_tcb != nil:
    val task = parent_tcb
    val is_blocked = match task.state:
        TaskState.Blocked(reason): true
        _: false
    expect(is_blocked).to_equal(true)
```

</details>

#### waitpid WNOHANG leaves live child and parent runnable

1. var scheduler = Scheduler new
2. scheduler schedule
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `0`
5. TaskState Blocked
   - Expected: is_blocked is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val child = scheduler.clone_task(parent)
val result = syscall_handler(
    SyscallArgs(
        id: 61,
        arg0: child.id,
        arg1: 0,
        arg2: 1,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(0)
val parent_tcb = scheduler.get_task(parent)
if parent_tcb != nil:
    val task = parent_tcb
    val is_blocked = match task.state:
        TaskState.Blocked(reason): true
        _: false
    expect(is_blocked).to_equal(false)
expect(scheduler.get_task(child)).to_be_nil.to_equal(false)
```

</details>

#### waitpid any child returns the reaped child pid

1. var scheduler = Scheduler new
2. scheduler schedule
3. scheduler schedule
4. scheduler exit task
5. IpcManager new
6. KernelLog new
   - Expected: result.value equals `child.id.to_i64()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val child = scheduler.clone_task(parent)
scheduler.schedule()
scheduler.exit_task(9)

val result = syscall_handler(
    SyscallArgs(
        id: 61,
        arg0: 0xFFFFFFFFFFFFFFFF,
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

expect(result.value).to_equal(child.id.to_i64())
expect(scheduler.get_task(child)).to_be_nil
```

</details>

#### waitpid writes encoded exit status before reaping child

1. var scheduler = Scheduler new
2. scheduler schedule
3. scheduler exit task by id
   - Expected: _map_user_pollfd_page(status_ptr) is true
4. IpcManager new
5. KernelLog new
   - Expected: result.value equals `child.id.to_i64()`
   - Expected: mmio_read32(status_ptr) equals `7u32 << 8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val child = scheduler.clone_task(parent)
scheduler.exit_task_by_id(child, 7)
val status_ptr: u64 = 0x70000000
expect(_map_user_pollfd_page(status_ptr)).to_equal(true)

val result = syscall_handler(
    SyscallArgs(
        id: 61,
        arg0: child.id,
        arg1: status_ptr,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(child.id.to_i64())
expect(mmio_read32(status_ptr)).to_equal(7u32 << 8)
expect(scheduler.get_task(child)).to_be_nil
```

</details>

#### waitpid rejects invalid status pointer without reaping zombie child

1. var scheduler = Scheduler new
2. scheduler schedule
3. scheduler exit task by id
4. IpcManager new
5. KernelLog new
   - Expected: result.value equals `-14`
   - Expected: is_zombie is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val child = scheduler.clone_task(parent)
scheduler.exit_task_by_id(child, 5)

val result = syscall_handler(
    SyscallArgs(
        id: 61,
        arg0: child.id,
        arg1: 1,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(-14)
val child_tcb = scheduler.get_task(child)
expect(child_tcb).to_be_nil.to_equal(false)
if child_tcb != nil:
    val task = child_tcb
    val is_zombie = match task.state:
        TaskState.Zombie: true
        _: false
    expect(is_zombie).to_equal(true)
```

</details>

#### waitpid syscall rejects missing children instead of returning ENOSYS

1. var scheduler = Scheduler new
2. scheduler create task
3. scheduler schedule
4. IpcManager new
5. KernelLog new
   - Expected: result.value equals `-10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val result = syscall_handler(
    SyscallArgs(
        id: 61,
        arg0: 999,
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
expect(result.value).to_equal(-10)
```

</details>

#### exec failure leaves current task image intact

1. var scheduler = Scheduler new
2. scheduler schedule
3. arg1: path len
4. IpcManager new
5. KernelLog new
   - Expected: result.value equals `-2`
   - Expected: current.is_user is false
   - Expected: current.entry_point equals `0x1234`
   - Expected: current.address_space equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1234, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val path = "/does/not/exist"

val result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(-2)
val tcb = scheduler.get_task(task)
if tcb != nil:
    val current = tcb
    expect(current.is_user).to_equal(false)
    expect(current.entry_point).to_equal(0x1234)
    expect(current.address_space).to_equal(0)
```

</details>

#### signal kill marks the target as a waitable zombie

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: kill_result.value equals `0`
   - Expected: status equals `-9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val child = scheduler.clone_task(parent)

val kill_result = syscall_handler(
    SyscallArgs(
        id: 7,
        arg0: child.id,
        arg1: 1,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(kill_result.value).to_equal(0)

val status = scheduler.wait_for(parent, child)
expect(status).to_equal(-9)
expect(scheduler.get_task(child)).to_be_nil
```

</details>

#### dynamic loading syscalls are wired instead of returning ENOSYS

1. dylib registry reset for test
2. arg1: missing path len
3. Scheduler new
4. IpcManager new
5. KernelLog new
   - Expected: open_result.value equals `-2`
6. arg2: missing sym len
7. Scheduler new
8. IpcManager new
9. KernelLog new
   - Expected: sym_result.value equals `-9`
10. Scheduler new
11. IpcManager new
12. KernelLog new
   - Expected: close_result.value equals `-9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dylib_registry_reset_for_test()
val missing_path = "/lib/missing.smf"
val missing_sym = "main"

val open_result = syscall_handler(
    SyscallArgs(
        id: 65,
        arg0: &missing_path as u64,
        arg1: missing_path.len() as u64,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    Scheduler.new(),
    IpcManager.new(),
    KernelLog.new(16)
)
expect(open_result.value).to_equal(-2)

val sym_result = syscall_handler(
    SyscallArgs(
        id: 66,
        arg0: 999,
        arg1: &missing_sym as u64,
        arg2: missing_sym.len() as u64,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    Scheduler.new(),
    IpcManager.new(),
    KernelLog.new(16)
)
expect(sym_result.value).to_equal(-9)

val close_result = syscall_handler(
    SyscallArgs(
        id: 67,
        arg0: 999,
        arg1: 0,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    Scheduler.new(),
    IpcManager.new(),
    KernelLog.new(16)
)
expect(close_result.value).to_equal(-9)
```

</details>

#### exec syscall replaces current task image and preserves pid

1. var scheduler = Scheduler new
2. scheduler schedule
3. arg1: path len
4. IpcManager new
5. KernelLog new
   - Expected: result.value equals `0`
   - Expected: tcb.is_user is true
   - Expected: tcb.id.id equals `task.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/services/vfs"
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(0)
val current = scheduler.get_task(task)
if current != nil:
    val tcb = current
    expect(tcb.is_user).to_equal(true)
    expect(tcb.id.id).to_equal(task.id)
```

</details>

#### exec syscall enforces AI CLI process grants before image replacement

1. set ai cli process manifest for test
2. var scheduler = Scheduler new
3. scheduler schedule
4. arg1: path len
5. IpcManager new
6. KernelLog new
   - Expected: result.value equals `-13`
   - Expected: tcb.is_user is false
   - Expected: tcb.entry_point equals `0x1000`
7. clear ai cli process manifest for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_ai_cli_process_manifest_for_test(codex_cli_smoke_manifest())
val path = "/sys/services/vfs"
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(-13)
val current = scheduler.get_task(task)
if current != nil:
    val tcb = current
    expect(tcb.is_user).to_equal(false)
    expect(tcb.entry_point).to_equal(0x1000)
clear_ai_cli_process_manifest_for_test()
```

</details>

#### exec syscall copies argv and envp vectors from userspace

1.  write user cstr
2.  write user cstr
3.  write user cstr
4. mmio write64
5. mmio write64
6. mmio write64
7. mmio write64
8. mmio write64
9. var scheduler = Scheduler new
10. scheduler schedule
11. arg1: path len
12. IpcManager new
13. KernelLog new
   - Expected: result.value equals `0`
   - Expected: tcb.is_user is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/services/vfs"
val argv_ptr = 0x10100000u64
val envp_ptr = 0x10101000u64
val arg0_ptr = 0x10100100u64
val arg1_ptr = 0x10100140u64
val env0_ptr = 0x10101100u64
expect(_map_user_pollfd_page(argv_ptr)).to_equal(true)
expect(_map_user_pollfd_page(envp_ptr)).to_equal(true)
_write_user_cstr(arg0_ptr, [0x76u8, 0x66u8, 0x73u8])
_write_user_cstr(arg1_ptr, [0x2Du8, 0x2Du8, 0x66u8, 0x67u8])
_write_user_cstr(env0_ptr, [0x53u8, 0x49u8, 0x4Du8, 0x50u8, 0x4Cu8, 0x45u8, 0x3Du8, 0x31u8])
mmio_write64(argv_ptr, arg0_ptr)
mmio_write64(argv_ptr + 8, arg1_ptr)
mmio_write64(argv_ptr + 16, 0)
mmio_write64(envp_ptr, env0_ptr)
mmio_write64(envp_ptr + 8, 0)

var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: argv_ptr,
        arg3: envp_ptr,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(0)
val current = scheduler.get_task(task)
if current != nil:
    val tcb = current
    expect(tcb.is_user).to_equal(true)
```

</details>

#### exec syscall rejects invalid argv and envp vector pointers

1. var argv scheduler = Scheduler new
2. argv scheduler create task
3. argv scheduler schedule
4. arg1: path len
5. IpcManager new
6. KernelLog new
   - Expected: argv_result.value equals `-14`
7. var envp scheduler = Scheduler new
8. envp scheduler create task
9. envp scheduler schedule
10. arg1: path len
11. IpcManager new
12. KernelLog new
   - Expected: envp_result.value equals `-14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/services/vfs"
var argv_scheduler = Scheduler.new()
argv_scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
argv_scheduler.schedule()
val argv_result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 1,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    argv_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(argv_result.value).to_equal(-14)

var envp_scheduler = Scheduler.new()
envp_scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
envp_scheduler.schedule()
val envp_result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 0,
        arg3: 1,
        arg4: 0,
        arg5: 0
    ),
    envp_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(envp_result.value).to_equal(-14)
```

</details>

#### exec syscall closes only close-on-exec descriptors on success

1. fd table init
2. var scheduler = Scheduler new
3. scheduler schedule
4. fd activate task
5. fd set
6. fd set
   - Expected: fd_set_cloexec(3, true) equals `0`
7. arg1: path len
8. IpcManager new
9. KernelLog new
   - Expected: result.value equals `0`
   - Expected: fd_is_valid(3) is false
   - Expected: fd_is_valid(4) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
val path = "/sys/services/vfs"
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
fd_activate_task(task.id)
fd_set(3, FD_TYPE_FILE, O_RDONLY, 30u64)
fd_set(4, FD_TYPE_FILE, O_RDONLY, 40u64)
expect(fd_set_cloexec(3, true)).to_equal(0)

val result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(0)
expect(fd_is_valid(3)).to_equal(false)
expect(fd_is_valid(4)).to_equal(true)
```

</details>

#### failed exec leaves close-on-exec descriptors open

1. fd table init
2. var scheduler = Scheduler new
3. scheduler schedule
4. fd activate task
5. fd set
   - Expected: fd_set_cloexec(3, true) equals `0`
6. arg1: path len
7. IpcManager new
8. KernelLog new
   - Expected: result.value equals `-2`
   - Expected: fd_is_valid(3) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
val path = "/sys/apps/does_not_exist"
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
fd_activate_task(task.id)
fd_set(3, FD_TYPE_FILE, O_RDONLY, 30u64)
expect(fd_set_cloexec(3, true)).to_equal(0)

val result = syscall_handler(
    SyscallArgs(
        id: 59,
        arg0: &path as u64,
        arg1: path.len() as u64,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)

expect(result.value).to_equal(-2)
expect(fd_is_valid(3)).to_equal(true)
```

</details>

#### queries scheduler policy through schedctl

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 0,
        arg1: task.id,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(0)
```

</details>

#### rejects deadline activation through schedctl v1

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `-95`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 1,
        arg1: task.id,
        arg2: 4,
        arg3: 1024,
        arg4: 1000000,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(-95)
```

</details>

#### requires RT bandwidth before schedctl RT activation

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: rejected.value equals `-22`
4. IpcManager new
5. KernelLog new
   - Expected: budget.value equals `0`
6. IpcManager new
7. KernelLog new
   - Expected: accepted.value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val rejected = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 1,
        arg1: task.id,
        arg2: 2,
        arg3: 1024,
        arg4: 1000000,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(rejected.value).to_equal(-22)

val budget = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 5,
        arg1: task.id,
        arg2: 0,
        arg3: 10000000,
        arg4: 30000000,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(budget.value).to_equal(0)

val accepted = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 1,
        arg1: task.id,
        arg2: 2,
        arg3: 1024,
        arg4: 1000000,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(accepted.value).to_equal(0)
```

</details>

#### admits deadline tasks through schedctl admission op

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `0`
4. IpcManager new
5. KernelLog new
   - Expected: query.value equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 4,
        arg1: task.id,
        arg2: 100000,
        arg3: 1000000,
        arg4: 500000,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(0)
val query = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 0,
        arg1: task.id,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(query.value).to_equal(4)
```

</details>

#### rejects invalid deadline schedctl admission parameters

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 4,
        arg1: task.id,
        arg2: 900000,
        arg3: 1000000,
        arg4: 500000,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(-22)
```

</details>

#### moves ready task to the CPU selected by schedctl affinity

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `0`
   - Expected: tcb.assigned_cpu equals `1u32`
   - Expected: tcb.schedule.affinity_mask equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 1,
        arg1: task.id,
        arg2: 0,
        arg3: 2048,
        arg4: 2000000,
        arg5: 2
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(0)
val updated = scheduler.get_task(task)
if updated != nil:
    val tcb = updated
    expect(tcb.assigned_cpu).to_equal(1u32)
    expect(tcb.schedule.affinity_mask).to_equal(2)
```

</details>

#### queries isolation generation through schedctl

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 2,
        arg1: task.id,
        arg2: 0,
        arg3: 0,
        arg4: 0,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(1)
```

</details>

#### restricts isolation resource caps through schedctl

1. var scheduler = Scheduler new
2. IpcManager new
3. KernelLog new
   - Expected: result.value equals `0`
   - Expected: tcb.isolation.capability_generation equals `2`
   - Expected: tcb.isolation.max_memory_pages equals `64`
   - Expected: tcb.isolation.max_threads equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
val result = syscall_handler(
    SyscallArgs(
        id: 107,
        arg0: 3,
        arg1: task.id,
        arg2: 0,
        arg3: 64,
        arg4: 1,
        arg5: 0
    ),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_equal(0)
val updated = scheduler.get_task(task)
if updated != nil:
    val tcb = updated
    expect(tcb.isolation.capability_generation).to_equal(2)
    expect(tcb.isolation.max_memory_pages).to_equal(64)
    expect(tcb.isolation.max_threads).to_equal(1u32)
```

</details>

#### updates isolation generation when pledge restricts current task

1. var scheduler = Scheduler new
2. scheduler schedule
3. IpcManager new
4. KernelLog new
   - Expected: result.value equals `0`
   - Expected: tcb.isolation.capability_generation equals `2`
   - Expected: tcb.isolation.allow_network is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var scheduler = Scheduler.new()
val task = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val result = syscall_handler(
    SyscallArgs(
        id: 40,
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
expect(result.value).to_equal(0)
val updated = scheduler.get_task(task)
if updated != nil:
    val tcb = updated
    expect(tcb.isolation.capability_generation).to_equal(2)
    expect(tcb.isolation.allow_network).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 47 |
| Active scenarios | 47 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
