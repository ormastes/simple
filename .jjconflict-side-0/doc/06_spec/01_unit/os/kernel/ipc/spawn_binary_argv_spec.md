# Spawn Binary Argv Specification

> 1.  clear synthetic vfs for test

<!-- sdn-diagram:id=spawn_binary_argv_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spawn_binary_argv_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spawn_binary_argv_spec -> std
spawn_binary_argv_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spawn_binary_argv_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spawn Binary Argv Specification

## Scenarios

### spawn_binary argv/envp

#### builds a larger initial user stack when argv and envp are provided

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. var default scheduler = Scheduler new
4. SyscallArgs
5. IpcManager new
6. KernelLog new
   - Expected: default_tcb == nil is false
   - Expected: argv_alloc == 0 is false
   - Expected: envp_alloc == 0 is false
7. rt ptr write i64
8. rt ptr write i64
9. rt ptr write i64
10. rt ptr write i64
11. rt ptr write i64
12. var arg scheduler = Scheduler new
13. SyscallArgs
14. IpcManager new
15. KernelLog new
   - Expected: arg_tcb == nil is false
   - Expected: default_task.is_user is true
   - Expected: arg_task.is_user is true
16. rt free
17. rt free
18.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 46 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/apps/hello_world"
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test(path, _make_x86_64_exec())

var default_scheduler = Scheduler.new()
val default_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 0, arg4: 0, arg5: 0),
    default_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(default_result.value).to_be_greater_than(0)
val default_tcb = default_scheduler.get_task(TaskId(id: default_result.value as u64))
expect(default_tcb == nil).to_equal(false)

val argv_alloc = rt_alloc(24)
val envp_alloc = rt_alloc(16)
expect(argv_alloc == 0).to_equal(false)
expect(envp_alloc == 0).to_equal(false)
rt_ptr_write_i64(argv_alloc, 0, rt_string_data("hello"))
rt_ptr_write_i64(argv_alloc, 8, rt_string_data("--flag"))
rt_ptr_write_i64(argv_alloc, 16, 0)
rt_ptr_write_i64(envp_alloc, 0, rt_string_data("TERM=simple"))
rt_ptr_write_i64(envp_alloc, 8, 0)

var arg_scheduler = Scheduler.new()
val arg_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: argv_alloc as u64, arg4: envp_alloc as u64, arg5: 0),
    arg_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(arg_result.value).to_be_greater_than(0)
val arg_tcb = arg_scheduler.get_task(TaskId(id: arg_result.value as u64))
expect(arg_tcb == nil).to_equal(false)

if default_tcb != nil and arg_tcb != nil:
    val default_task = default_tcb
    val arg_task = arg_tcb
    expect(default_task.is_user).to_equal(true)
    expect(arg_task.is_user).to_equal(true)
    expect(arg_task.context.rsp).to_be_less_than(default_task.context.rsp)

rt_free(argv_alloc)
rt_free(envp_alloc)
_clear_synthetic_vfs_for_test()
```

</details>

#### rejects invalid argv and envp vector pointers

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. var argv scheduler = Scheduler new
4. SyscallArgs
5. IpcManager new
6. KernelLog new
   - Expected: argv_result.value equals `-14`
7. var envp scheduler = Scheduler new
8. SyscallArgs
9. IpcManager new
10. KernelLog new
   - Expected: envp_result.value equals `-14`
11.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/sys/apps/hello_world"
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test(path, _make_x86_64_exec())

var argv_scheduler = Scheduler.new()
val argv_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 1, arg4: 0, arg5: 0),
    argv_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(argv_result.value).to_equal(-14)

var envp_scheduler = Scheduler.new()
val envp_result = syscall_handler(
    SyscallArgs(id: 13, arg0: rt_string_data(path) as u64, arg1: path.len() as u64, arg2: 2, arg3: 0, arg4: 1, arg5: 0),
    envp_scheduler,
    IpcManager.new(),
    KernelLog.new(16)
)
expect(envp_result.value).to_equal(-14)
_clear_synthetic_vfs_for_test()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/spawn_binary_argv_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- spawn_binary argv/envp

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
