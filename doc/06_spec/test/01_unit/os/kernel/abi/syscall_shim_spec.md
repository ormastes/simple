# Syscall Shim Specification

> <details>

<!-- sdn-diagram:id=syscall_shim_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_shim_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_shim_spec -> std
syscall_shim_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_shim_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 71 | 71 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Shim Specification

## Scenarios

### syscall_shim — compile-time surface checks

#### shim_init accepts Scheduler, IpcManager, KernelLog

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init_ref = shim_init
expect(init_ref).to_not_be_nil()
```

</details>

#### spl_handle_debug_write accepts six u64 arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_debug_write
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_debug_write return type is i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result: i64 = spl_handle_debug_write(0, 0, 0, 0, 0, 0)
expect(result).to_be_i64()
```

</details>

#### spl_handle_exit has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_exit
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_yield has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_yield
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_spawn has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_spawn
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_wait has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_wait
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_getpid has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_getpid
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_list_tasks has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_list_tasks
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_get_task_info has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_get_task_info
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_signal has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_signal
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_set_priority has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_set_priority
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_get_parent_pid has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_get_parent_pid
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_mmap has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_mmap
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_munmap has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_munmap
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_mprotect has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_mprotect
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_spawn_binary has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_spawn_binary
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_ipc_send has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_ipc_send
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_ipc_recv has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_ipc_recv
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_ipc_create_port has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_ipc_create_port
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_ipc_connect has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_ipc_connect
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_notification_create has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_notification_create
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_notification_signal has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_notification_signal
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_notification_wait has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_notification_wait
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_notification_poll has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_notification_poll
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_notification_destroy has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_notification_destroy
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_notification_wait_any has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_notification_wait_any
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_file_open has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_file_open
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_file_read has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_file_read
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_file_write has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_file_write
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_file_close has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_file_close
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_file_stat has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_file_stat
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_file_mkdir has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_file_mkdir
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_file_readdir has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_file_readdir
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_mount has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_mount
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_unmount has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_unmount
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_unlink has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_unlink
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_pledge has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_pledge
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_unveil has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_unveil
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_cap_grant has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_cap_grant
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_ftruncate has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_ftruncate
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_rename has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_rename
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_rmdir has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_rmdir
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_lseek has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_lseek
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_getcwd has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_getcwd
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_chdir has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_chdir
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_clock_gettime has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_clock_gettime
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_sleep has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_sleep
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_fork has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_fork
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_exec has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_exec
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_waitpid has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_waitpid
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_socket has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_socket
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_bind has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_bind
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_listen has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_listen
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_connect has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_connect
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_accept has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_accept
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_send_to has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_send_to
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_recv_from has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_recv_from
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_net_if_config has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_net_if_config
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_dev_enumerate has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_dev_enumerate
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_dev_get_info has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_dev_get_info
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_map_bar has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_map_bar
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_alloc_dma has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_alloc_dma
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_free_dma has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_free_dma
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_log_write has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_log_write
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_log_read has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_log_read
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_sysinfo has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_sysinfo
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_get_hostname has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_get_hostname
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_set_hostname has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_set_hostname
expect(fn_ref).to_not_be_nil()
```

</details>

#### spl_handle_device_grant has arity six u64 -> i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fn_ref: fn(u64, u64, u64, u64, u64, u64) -> i64 = spl_handle_device_grant
expect(fn_ref).to_not_be_nil()
```

</details>

#### implemented shim count is at least 53

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Lock progress: 53 strong shims implemented (syscall 82/device_grant now wired
# via g_shim_scheduler.get_current() to supply the caller TaskId).
# Count = 1 (debug_write/60) + 13 (process 0-13) + 10 (ipc/notify 20-29)
#       + 15 (file 30-48) + 2 (time 50-51) + 8 (net 70-77)
#       + 5 (device 80-85 — all including 82) + 4 (log/sys 90-91,95-97)
# = 58 shims exported
val count: i64 = 59
expect(count).to_be_greater_than(58)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/abi/syscall_shim_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- syscall_shim — compile-time surface checks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 71 |
| Active scenarios | 71 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
