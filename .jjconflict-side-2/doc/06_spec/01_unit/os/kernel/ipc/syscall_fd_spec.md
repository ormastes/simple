# POSIX fd syscall dispatch

> Syscalls 62, 63, and 64 provide pipe, dup2, and dup to libc.

<!-- sdn-diagram:id=syscall_fd_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_fd_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_fd_spec -> std
syscall_fd_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_fd_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# POSIX fd syscall dispatch

Syscalls 62, 63, and 64 provide pipe, dup2, and dup to libc.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/syscall_fd_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Syscalls 62, 63, and 64 provide pipe, dup2, and dup to libc.

## Scenarios

### POSIX fd syscalls

#### provides syscall 64 dup through the dispatcher

1. fd table init
2. fd set
   - Expected: fd_set_offset(3, 21u64) equals `0`
   - Expected: result equals `4`
   - Expected: fd_is_valid(4) is true
   - Expected: fd_get_offset(4) equals `21u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
expect(fd_set_offset(3, 21u64)).to_equal(0)

val result = _dispatch(SyscallArgs(id: 64, arg0: 3, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))

expect(result).to_equal(4)
expect(fd_is_valid(4)).to_equal(true)
expect(fd_get_offset(4)).to_equal(21u64)
```

</details>

#### provides syscall 63 dup2 replacement through the dispatcher

1. fd table init
2. fd set
3. fd set
   - Expected: fd_set_offset(3, 34u64) equals `0`
   - Expected: result equals `4`
   - Expected: fd_get_offset(4) equals `34u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
fd_set(4, FD_TYPE_FILE, O_RDONLY, 20u64)
expect(fd_set_offset(3, 34u64)).to_equal(0)

val result = _dispatch(SyscallArgs(id: 63, arg0: 3, arg1: 4, arg2: 0, arg3: 0, arg4: 0, arg5: 0))

expect(result).to_equal(4)
expect(fd_get_offset(4)).to_equal(34u64)
```

</details>

#### provides syscall 62 pipe and validates the output pointer

1. fd table init
   - Expected: result equals `-14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()

val result = _dispatch(SyscallArgs(id: 62, arg0: 0, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))

expect(result).to_equal(-14)
```

</details>

#### routes syscall 31 and 32 through the native pipe fd backend

1. fd table init
2. pipe init
   - Expected: posix_pipe(unsafe_addr_of(read_fd), unsafe_addr_of(write_fd)) equals `0`
   - Expected: _map_user_page(write_ptr) is true
   - Expected: _map_user_page(read_ptr) is true
3. mmio write8
4. mmio write8
   - Expected: written equals `2`
   - Expected: read equals `2`
   - Expected: mmio_read8(read_ptr) equals `0x68u8`
   - Expected: mmio_read8(read_ptr + 1) equals `0x69u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
pipe_init()
var read_fd: i32 = 0
var write_fd: i32 = 0
expect(posix_pipe(unsafe_addr_of(read_fd), unsafe_addr_of(write_fd))).to_equal(0)

val write_ptr = 0x10002000u64
val read_ptr = 0x10003000u64
expect(_map_user_page(write_ptr)).to_equal(true)
expect(_map_user_page(read_ptr)).to_equal(true)
mmio_write8(write_ptr, 0x68)
mmio_write8(write_ptr + 1, 0x69)

val written = _dispatch(SyscallArgs(id: 32, arg0: write_fd as u64, arg1: write_ptr, arg2: 2, arg3: 0, arg4: 0, arg5: 0))
val read = _dispatch(SyscallArgs(id: 31, arg0: read_fd as u64, arg1: read_ptr, arg2: 2, arg3: 0, arg4: 0, arg5: 0))

expect(written).to_equal(2)
expect(read).to_equal(2)
expect(mmio_read8(read_ptr)).to_equal(0x68u8)
expect(mmio_read8(read_ptr + 1)).to_equal(0x69u8)
```

</details>

#### rejects non-empty read and write syscall kernel pointers

1. fd table init
   - Expected: _dispatch(SyscallArgs(id: 31, arg0: 3, arg1: 0xC0000000, arg2: 1, arg3: 0, arg4: 0, arg5: 0)) equals `-14`
   - Expected: _dispatch(SyscallArgs(id: 32, arg0: 3, arg1: 0xC0000000, arg2: 1, arg3: 0, arg4: 0, arg5: 0)) equals `-14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()

expect(_dispatch(SyscallArgs(id: 31, arg0: 3, arg1: 0xC0000000, arg2: 1, arg3: 0, arg4: 0, arg5: 0))).to_equal(-14)
expect(_dispatch(SyscallArgs(id: 32, arg0: 3, arg1: 0xC0000000, arg2: 1, arg3: 0, arg4: 0, arg5: 0))).to_equal(-14)
```

</details>

#### provides syscall 33 close through the fd table

1. fd table init
2. fd set
   - Expected: result equals `0`
   - Expected: fd_is_valid(3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)

val result = _dispatch(SyscallArgs(id: 33, arg0: 3, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))

expect(result).to_equal(0)
expect(fd_is_valid(3)).to_equal(false)
```

</details>

#### provides syscall 69 fcntl descriptor flags

1. fd table init
2. fd set
   - Expected: _dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 1, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) equals `0`
   - Expected: _dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 2, arg2: 1, arg3: 0, arg4: 0, arg5: 0)) equals `0`
   - Expected: fd_get_cloexec(3) is true
   - Expected: _dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 1, arg2: 0, arg3: 0, arg4: 0, arg5: 0)) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)

expect(_dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 1, arg2: 0, arg3: 0, arg4: 0, arg5: 0))).to_equal(0)
expect(_dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 2, arg2: 1, arg3: 0, arg4: 0, arg5: 0))).to_equal(0)
expect(fd_get_cloexec(3)).to_equal(true)
expect(_dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 1, arg2: 0, arg3: 0, arg4: 0, arg5: 0))).to_equal(1)
```

</details>

#### provides syscall 69 fcntl status flags and min-fd duplication

1. fd table init
2. fd set
   - Expected: _dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 4, arg2: O_RDWR | O_NONBLOCK, arg3: 0, arg4: 0, arg5: 0)) equals `0`
   - Expected: fd_get_status_flags(3) & O_NONBLOCK equals `O_NONBLOCK`
   - Expected: dup_fd equals `8`
   - Expected: fd_is_valid(8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDWR, 10u64)

expect(_dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 4, arg2: O_RDWR | O_NONBLOCK, arg3: 0, arg4: 0, arg5: 0))).to_equal(0)
expect(fd_get_status_flags(3) & O_NONBLOCK).to_equal(O_NONBLOCK)

val dup_fd = _dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 0, arg2: 8, arg3: 0, arg4: 0, arg5: 0))
expect(dup_fd).to_equal(8)
expect(fd_is_valid(8)).to_equal(true)
```

</details>

#### provides syscall 69 F_DUPFD_CLOEXEC

1. fd table init
2. fd set
   - Expected: result equals `8`
   - Expected: fd_is_valid(8) is true
   - Expected: fd_get_cloexec(8) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)

val result = _dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 1030, arg2: 8, arg3: 0, arg4: 0, arg5: 0))

expect(result).to_equal(8)
expect(fd_is_valid(8)).to_equal(true)
expect(fd_get_cloexec(8)).to_equal(true)
```

</details>

#### provides syscall 69 SimpleOS open-file-description token

1. fd table init
2. fd set
   - Expected: dup_token equals `token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)

val token = _dispatch(SyscallArgs(id: 69, arg0: 3, arg1: 1397686273, arg2: 0, arg3: 0, arg4: 0, arg5: 0))
val dup_fd = _dispatch(SyscallArgs(id: 64, arg0: 3, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0))
val dup_token = _dispatch(SyscallArgs(id: 69, arg0: dup_fd as u64, arg1: 1397686273, arg2: 0, arg3: 0, arg4: 0, arg5: 0))

expect(token).to_be_greater_than(0)
expect(dup_token).to_equal(token)
```

</details>

#### activates descriptor context for the current scheduler task

1. fd table init
2. var scheduler = Scheduler new
3. scheduler schedule
4. fd activate task
5. fd set
6. SyscallArgs
7. IpcManager new
8. KernelLog new
   - Expected: parent_dup equals `4`
9. scheduler schedule
10. SyscallArgs
11. IpcManager new
12. KernelLog new
   - Expected: child_dup equals `-9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
var scheduler = Scheduler.new()
val parent = scheduler.create_task(0x1000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
fd_activate_task(parent.id)
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)

val parent_dup = syscall_handler(
    SyscallArgs(id: 64, arg0: 3, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
).value
expect(parent_dup).to_equal(4)

val child = scheduler.create_task(0x2000, TaskPriority.Normal, CapabilitySet.full())
scheduler.schedule()
val child_dup = syscall_handler(
    SyscallArgs(id: 64, arg0: 3, arg1: 0, arg2: 0, arg3: 0, arg4: 0, arg5: 0),
    scheduler,
    IpcManager.new(),
    KernelLog.new(16)
).value

expect(child.id).to_be_greater_than(0)
expect(child_dup).to_equal(-9)
```

</details>

#### provides syscall 68 poll and validates the pollfd pointer

1. fd table init
   - Expected: result equals `-14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()

val result = _dispatch(SyscallArgs(id: 68, arg0: 0, arg1: 1, arg2: 0, arg3: 0, arg4: 0, arg5: 0))

expect(result).to_equal(-14)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
