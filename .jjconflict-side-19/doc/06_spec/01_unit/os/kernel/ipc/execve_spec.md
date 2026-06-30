# execve_spec

> Execve Syscall Specification

<!-- sdn-diagram:id=execve_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=execve_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

execve_spec -> std
execve_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=execve_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# execve_spec

Execve Syscall Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/execve_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Execve Syscall Specification

Tests for the execve (sys_exec, syscall 59) implementation that replaces
the current process image in-place while preserving PID and file descriptors.

## Scenarios

### execve syscall

#### dispatches exec (syscall 59) with valid path and replaces process image

1. fd table init
2.  clear synthetic vfs for test
3.  set synthetic vfs file for test
4. var sched = Scheduler new
5. SyscallArgs
6. IpcManager new
7. KernelLog new
8. SyscallArgs
9. IpcManager new
10. KernelLog new
   - Expected: exec_result.value equals `0`
11.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
val path = "/sys/apps/hello_world"
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test(path, _make_x86_64_exec())

# First spawn a process that will call exec
var sched = Scheduler.new()
val spawn_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(spawn_result.value).to_be_greater_than(0)
val spawned_pid = spawn_result.value as u64

# Now call exec (syscall 59) to replace the image
val exec_result = syscall_handler(
    SyscallArgs(id: 59, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
# exec returns 0 on success
expect(exec_result.value).to_equal(0)
_clear_synthetic_vfs_for_test()
```

</details>

### execve error handling

#### returns ENOENT for non-existent executable path

1. fd table init
2.  clear synthetic vfs for test
3. var sched = Scheduler new
4. SyscallArgs
5. IpcManager new
6. KernelLog new
   - Expected: result.value equals `-2`
7.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
_clear_synthetic_vfs_for_test()
val bad_path = "/sys/apps/does_not_exist"
var sched = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(id: 59, arg0: rt_string_data(bad_path) as u64, arg1: bad_path.len() as u64, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
# -2 is ENOENT (file not found)
expect(result.value).to_equal(-2)
_clear_synthetic_vfs_for_test()
```

</details>

#### returns ENOEXEC for invalid ELF data

1. fd table init
2.  clear synthetic vfs for test
3. bad bytes push
4.  set synthetic vfs file for test
5. var sched = Scheduler new
6. SyscallArgs
7. IpcManager new
8. KernelLog new
   - Expected: result.value equals `-8`
9.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
_clear_synthetic_vfs_for_test()
val path = "/sys/apps/bad_binary"
# Register a file with invalid ELF content (just random bytes)
var bad_bytes: [u8] = []
var bi = 0
while bi < 64:
    bad_bytes.push(0xDE.to_u8())
    bi = bi + 1
_set_synthetic_vfs_file_for_test(path, bad_bytes)

var sched = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(id: 59, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
# -8 is ENOEXEC (exec format error, image build failed)
expect(result.value).to_equal(-8)
_clear_synthetic_vfs_for_test()
```

</details>

#### returns EINVAL when path pointer is null

1. fd table init
2. var sched = Scheduler new
3. SyscallArgs
4. IpcManager new
5. KernelLog new


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
var sched = Scheduler.new()
val result = syscall_handler(
    SyscallArgs(id: 59, arg0: 0, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
# arg0==0 or arg1==0 returns -EINVAL
expect(result.value).to_be_less_than(0)
```

</details>

#### returns ENAMETOOLONG when path exceeds maximum length

1. fd table init
2. var sched = Scheduler new
3. SyscallArgs
4. IpcManager new
5. KernelLog new


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
var sched = Scheduler.new()
# Path length > MAX_BINARY_PATH_LEN (256)
val result = syscall_handler(
    SyscallArgs(id: 59, arg0: 1, arg1: 1024, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(result.value).to_be_less_than(0)
```

</details>

### execve PID preservation

#### preserves task PID across exec (structural assertion)

1. fd table init
2.  clear synthetic vfs for test
3.  set synthetic vfs file for test
4. var sched = Scheduler new
5. SyscallArgs
6. IpcManager new
7. KernelLog new
   - Expected: tcb_before == nil is false
8. SyscallArgs
9. IpcManager new
10. KernelLog new
   - Expected: exec_result.value equals `0`
   - Expected: tcb_after == nil is false
   - Expected: task.id.id equals `pid_before`
   - Expected: task.is_user is true
11.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
val path = "/sys/apps/hello_world"
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test(path, _make_x86_64_exec())

# Spawn a task first
var sched = Scheduler.new()
val spawn_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(spawn_result.value).to_be_greater_than(0)
val pid_before = spawn_result.value as u64
val tcb_before = sched.get_task(TaskId(id: pid_before))
expect(tcb_before == nil).to_equal(false)

# Exec replaces the image; scheduler.exec_image preserves TaskId
val exec_result = syscall_handler(
    SyscallArgs(id: 59, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    sched,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(exec_result.value).to_equal(0)

# The task at the same PID slot must still exist
val tcb_after = sched.get_task(TaskId(id: pid_before))
expect(tcb_after == nil).to_equal(false)
if tcb_after != nil:
    val task = tcb_after
    expect(task.id.id).to_equal(pid_before)
    expect(task.is_user).to_equal(true)
_clear_synthetic_vfs_for_test()
```

</details>

### vmm_teardown_user_space

#### clears all VMAs from a process address space

1. var space = vmm new process space
   - Expected: space.vma_count as i64 equals `2`
   - Expected: space.areas.len() equals `2`
2. vmm teardown user space
   - Expected: space.vma_count as i64 equals `0`
   - Expected: space.areas.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = vmm_new_process_space(0, 1)
# Add some test VMAs
space.areas.push(VmArea(
    start: 0x400000,
    len: 0x1000,
    kind: VMA_ANON,
    flags: VMA_READ | VMA_EXEC,
    backing: 0,
    backing_offset: 0
))
space.vma_count = 1
space.areas.push(VmArea(
    start: 0x7FFF0000,
    len: 0x10000,
    kind: VMA_ANON,
    flags: VMA_READ | VMA_WRITE,
    backing: 0,
    backing_offset: 0
))
space.vma_count = 2

expect(space.vma_count as i64).to_equal(2)
expect(space.areas.len()).to_equal(2)

vmm_teardown_user_space(space)

expect(space.vma_count as i64).to_equal(0)
expect(space.areas.len()).to_equal(0)
```

</details>

#### handles an already-empty address space

1. var space = vmm new process space
   - Expected: space.vma_count as i64 equals `0`
2. vmm teardown user space
   - Expected: space.vma_count as i64 equals `0`
   - Expected: space.areas.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var space = vmm_new_process_space(0, 2)
expect(space.vma_count as i64).to_equal(0)
vmm_teardown_user_space(space)
expect(space.vma_count as i64).to_equal(0)
expect(space.areas.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
