# POSIX fd table specification

> The fd table maps descriptors to open file descriptions. Duplicated

<!-- sdn-diagram:id=fd_table_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fd_table_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fd_table_spec -> std
fd_table_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fd_table_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# POSIX fd table specification

The fd table maps descriptors to open file descriptions. Duplicated

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/posix/fd_table_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

The fd table maps descriptors to open file descriptions. Duplicated
descriptors share status flags and file offsets, while FD_CLOEXEC remains
per descriptor.

## Scenarios

### POSIX fd table

#### initializes stdio descriptors and allocates the lowest free descriptor

1. fd table init
   - Expected: fd_is_valid(0) is true
   - Expected: fd_is_valid(1) is true
   - Expected: fd_is_valid(2) is true
   - Expected: fd_types[0] equals `FD_TYPE_SERIAL`
   - Expected: fd_alloc() equals `3`
   - Expected: fd_close(0) equals `0`
   - Expected: fd_alloc() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()

expect(fd_is_valid(0)).to_equal(true)
expect(fd_is_valid(1)).to_equal(true)
expect(fd_is_valid(2)).to_equal(true)
expect(fd_types[0]).to_equal(FD_TYPE_SERIAL)
expect(fd_alloc()).to_equal(3)

expect(fd_close(0)).to_equal(0)
expect(fd_alloc()).to_equal(0)
```

</details>

#### keeps O_CLOEXEC as a per-descriptor flag

1. fd table init
   - Expected: fd_set(3, FD_TYPE_FILE, O_RDWR | O_NONBLOCK | O_CLOEXEC, 99u64) equals `0`
   - Expected: fd_get_cloexec(3) is true
   - Expected: fd_get_status_flags(3) & O_CLOEXEC equals `0u32`
   - Expected: fd_get_status_flags(3) & O_NONBLOCK equals `O_NONBLOCK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
expect(fd_set(3, FD_TYPE_FILE, O_RDWR | O_NONBLOCK | O_CLOEXEC, 99u64)).to_equal(0)

expect(fd_get_cloexec(3)).to_equal(true)
expect(fd_get_status_flags(3) & O_CLOEXEC).to_equal(0u32)
expect(fd_get_status_flags(3) & O_NONBLOCK).to_equal(O_NONBLOCK)
```

</details>

#### reports open-file-description exhaustion through fd_set

1. fd table init
   - Expected: fd_set(fd, FD_TYPE_FILE, O_RDONLY, fd as u64) equals `0`
   - Expected: fd_set(255, FD_TYPE_FILE, O_RDONLY, 255u64) equals `0 - EMFILE`
   - Expected: fd_is_valid(255) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
var fd: i32 = 3
while (fd as u64) < MAX_FDS - 1:
    expect(fd_set(fd, FD_TYPE_FILE, O_RDONLY, fd as u64)).to_equal(0)
    fd = fd + 1

expect(fd_set(255, FD_TYPE_FILE, O_RDONLY, 255u64)).to_equal(0 - EMFILE)
expect(fd_is_valid(255)).to_equal(false)
```

</details>

#### duplicates descriptors onto a shared open file description

1. fd table init
2. fd set
   - Expected: fd_set_offset(3, 44u64) equals `0`
   - Expected: fd_set_status_flags(3, O_RDWR | O_NONBLOCK) equals `0`
   - Expected: dup_fd equals `4`
   - Expected: fd_get_cloexec(dup_fd) is false
   - Expected: fd_refcounts[3] equals `2u32`
   - Expected: fd_refcounts[4] equals `2u32`
   - Expected: fd_get_offset(dup_fd) equals `44u64`
   - Expected: fd_get_status_flags(dup_fd) & O_NONBLOCK equals `O_NONBLOCK`
   - Expected: fd_set_offset(dup_fd, 88u64) equals `0`
   - Expected: fd_get_offset(3) equals `88u64`
   - Expected: fd_set_status_flags(dup_fd, O_RDWR) equals `0`
   - Expected: fd_get_status_flags(3) & O_NONBLOCK equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDWR | O_CLOEXEC, 99u64)
expect(fd_set_offset(3, 44u64)).to_equal(0)
expect(fd_set_status_flags(3, O_RDWR | O_NONBLOCK)).to_equal(0)

val dup_fd = fd_dup(3)

expect(dup_fd).to_equal(4)
expect(fd_get_cloexec(dup_fd)).to_equal(false)
expect(fd_refcounts[3]).to_equal(2u32)
expect(fd_refcounts[4]).to_equal(2u32)
expect(fd_get_offset(dup_fd)).to_equal(44u64)
expect(fd_get_status_flags(dup_fd) & O_NONBLOCK).to_equal(O_NONBLOCK)

expect(fd_set_offset(dup_fd, 88u64)).to_equal(0)
expect(fd_get_offset(3)).to_equal(88u64)

expect(fd_set_status_flags(dup_fd, O_RDWR)).to_equal(0)
expect(fd_get_status_flags(3) & O_NONBLOCK).to_equal(0u32)
```

</details>

#### exposes a stable token for duplicated open file descriptions

1. fd table init
2. fd set
   - Expected: dup_fd equals `4`
   - Expected: fd_get_object_id(dup_fd) equals `original_token`
3. fd set
   - Expected: fd_get_object_id(5) equals `20u64`
   - Expected: fd_dup2(3, 5) equals `5`
   - Expected: fd_get_object_id(5) equals `original_token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
val original_token = fd_get_object_id(3)

val dup_fd = fd_dup(3)
expect(dup_fd).to_equal(4)
expect(fd_get_object_id(dup_fd)).to_equal(original_token)

fd_set(5, FD_TYPE_FILE, O_RDONLY, 20u64)
expect(fd_get_object_id(5)).to_equal(20u64)
expect(fd_dup2(3, 5)).to_equal(5)
expect(fd_get_object_id(5)).to_equal(original_token)
```

</details>

#### implements dup2 replacement semantics

1. fd table init
2. fd set
3. fd set
   - Expected: fd_set_offset(3, 7u64) equals `0`
   - Expected: fd_set_offset(4, 99u64) equals `0`
   - Expected: fd_dup2(3, 4) equals `4`
   - Expected: fd_ports[4] equals `10u64`
   - Expected: fd_get_cloexec(4) is false
   - Expected: fd_refcounts[3] equals `2u32`
   - Expected: fd_refcounts[4] equals `2u32`
   - Expected: fd_get_offset(4) equals `7u64`
   - Expected: fd_set_offset(4, 12u64) equals `0`
   - Expected: fd_get_offset(3) equals `12u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
fd_set(4, FD_TYPE_FILE, O_WRONLY | O_CLOEXEC, 20u64)
expect(fd_set_offset(3, 7u64)).to_equal(0)
expect(fd_set_offset(4, 99u64)).to_equal(0)

expect(fd_dup2(3, 4)).to_equal(4)

expect(fd_ports[4]).to_equal(10u64)
expect(fd_get_cloexec(4)).to_equal(false)
expect(fd_refcounts[3]).to_equal(2u32)
expect(fd_refcounts[4]).to_equal(2u32)
expect(fd_get_offset(4)).to_equal(7u64)

expect(fd_set_offset(4, 12u64)).to_equal(0)
expect(fd_get_offset(3)).to_equal(12u64)
```

</details>

#### preserves descriptor flags when dup2 targets the same descriptor

1. fd table init
2. fd set
   - Expected: fd_dup2(3, 3) equals `3`
   - Expected: fd_get_cloexec(3) is true
   - Expected: fd_refcounts[3] equals `1u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY | O_CLOEXEC, 10u64)

expect(fd_dup2(3, 3)).to_equal(3)
expect(fd_get_cloexec(3)).to_equal(true)
expect(fd_refcounts[3]).to_equal(1u32)
```

</details>

#### rejects invalid dup descriptors with EBADF

1. fd table init
2. fd set
   - Expected: fd_dup(-1) equals `0 - EBADF`
   - Expected: fd_dup2(99, 4) equals `0 - EBADF`
   - Expected: fd_dup2(3, -1) equals `0 - EBADF`
   - Expected: fd_dup2(3, 256) equals `0 - EBADF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)

expect(fd_dup(-1)).to_equal(0 - EBADF)
expect(fd_dup2(99, 4)).to_equal(0 - EBADF)
expect(fd_dup2(3, -1)).to_equal(0 - EBADF)
expect(fd_dup2(3, 256)).to_equal(0 - EBADF)
```

</details>

#### closes only descriptors marked close-on-exec

1. fd table init
2. fd set
3. fd set
   - Expected: fd_set_cloexec(3, true) equals `0`
   - Expected: fd_set_cloexec(4, false) equals `0`
   - Expected: fd_close_on_exec() equals `1u32`
   - Expected: fd_is_valid(3) is false
   - Expected: fd_is_valid(4) is true
   - Expected: fd_types[3] equals `FD_TYPE_FREE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
fd_set(4, FD_TYPE_FILE, O_RDONLY, 20u64)
expect(fd_set_cloexec(3, true)).to_equal(0)
expect(fd_set_cloexec(4, false)).to_equal(0)

expect(fd_close_on_exec()).to_equal(1u32)
expect(fd_is_valid(3)).to_equal(false)
expect(fd_is_valid(4)).to_equal(true)
expect(fd_types[3]).to_equal(FD_TYPE_FREE)
```

</details>

#### applies exec cleanup through the exec lifecycle alias

1. fd table init
2. fd set
3. fd set
   - Expected: fd_exec_cleanup() equals `1u32`
   - Expected: fd_is_valid(3) is false
   - Expected: fd_is_valid(4) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY | O_CLOEXEC, 10u64)
fd_set(4, FD_TYPE_FILE, O_RDONLY, 20u64)

expect(fd_exec_cleanup()).to_equal(1u32)
expect(fd_is_valid(3)).to_equal(false)
expect(fd_is_valid(4)).to_equal(true)
```

</details>

#### inherits live descriptors across fork without changing cloexec flags

1. fd table init
2. fd set
3. fd set
   - Expected: fd_get_refcount(3) equals `1u32`
   - Expected: fd_prepare_fork() equals `5u32`
   - Expected: fd_get_refcount(3) equals `2u32`
   - Expected: fd_get_refcount(4) equals `2u32`
   - Expected: fd_get_cloexec(3) is true
   - Expected: fd_get_cloexec(4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY | O_CLOEXEC, 10u64)
fd_set(4, FD_TYPE_FILE, O_WRONLY, 20u64)

expect(fd_get_refcount(3)).to_equal(1u32)
expect(fd_prepare_fork()).to_equal(5u32)

expect(fd_get_refcount(3)).to_equal(2u32)
expect(fd_get_refcount(4)).to_equal(2u32)
expect(fd_get_cloexec(3)).to_equal(true)
expect(fd_get_cloexec(4)).to_equal(false)
```

</details>

#### releases every live descriptor on process exit

1. fd table init
2. fd set
3. fd set
   - Expected: fd_release_on_process_exit() equals `5u32`
   - Expected: fd_is_valid(0) is false
   - Expected: fd_is_valid(3) is false
   - Expected: fd_is_valid(4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
fd_set(4, FD_TYPE_FILE, O_WRONLY, 20u64)

expect(fd_release_on_process_exit()).to_equal(5u32)
expect(fd_is_valid(0)).to_equal(false)
expect(fd_is_valid(3)).to_equal(false)
expect(fd_is_valid(4)).to_equal(false)
```

</details>

#### keeps descriptor tables isolated between active tasks

1. fd table init
2. fd activate task
3. fd set
   - Expected: fd_current_task() equals `10u64`
   - Expected: fd_is_valid(3) is true
4. fd activate task
   - Expected: fd_current_task() equals `11u64`
   - Expected: fd_is_valid(3) is false
   - Expected: fd_is_valid(0) is true
5. fd activate task
   - Expected: fd_is_valid(3) is true
   - Expected: fd_get_backend_handle(3) equals `10u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_activate_task(10u64)
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
expect(fd_current_task()).to_equal(10u64)
expect(fd_is_valid(3)).to_equal(true)

fd_activate_task(11u64)
expect(fd_current_task()).to_equal(11u64)
expect(fd_is_valid(3)).to_equal(false)
expect(fd_is_valid(0)).to_equal(true)

fd_activate_task(10u64)
expect(fd_is_valid(3)).to_equal(true)
expect(fd_get_backend_handle(3)).to_equal(10u64)
```

</details>

#### does not alias descriptor contexts with modulo-colliding task ids

1. fd table init
2. fd activate task
3. fd set
4. fd activate task
   - Expected: fd_current_task() equals `266u64`
   - Expected: fd_is_valid(3) is false
5. fd set
6. fd activate task
   - Expected: fd_is_valid(3) is true
   - Expected: fd_get_backend_handle(3) equals `10u64`
7. fd activate task
   - Expected: fd_is_valid(3) is true
   - Expected: fd_get_backend_handle(3) equals `266u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_activate_task(10u64)
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)

fd_activate_task(266u64)
expect(fd_current_task()).to_equal(266u64)
expect(fd_is_valid(3)).to_equal(false)
fd_set(3, FD_TYPE_FILE, O_RDONLY, 266u64)

fd_activate_task(10u64)
expect(fd_is_valid(3)).to_equal(true)
expect(fd_get_backend_handle(3)).to_equal(10u64)

fd_activate_task(266u64)
expect(fd_is_valid(3)).to_equal(true)
expect(fd_get_backend_handle(3)).to_equal(266u64)
```

</details>

#### clones active descriptor table into fork child context

1. fd table init
2. fd activate task
3. fd set
   - Expected: fd_set_offset(3, 44u64) equals `0`
   - Expected: fd_prepare_fork_to_task(21u64) equals `4u32`
   - Expected: fd_get_refcount(3) equals `2u32`
4. fd activate task
   - Expected: fd_is_valid(3) is true
   - Expected: fd_get_cloexec(3) is true
   - Expected: fd_get_offset(3) equals `44u64`
   - Expected: fd_set_offset(3, 88u64) equals `0`
5. fd activate task
   - Expected: fd_get_offset(3) equals `88u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_activate_task(20u64)
fd_set(3, FD_TYPE_FILE, O_RDONLY | O_CLOEXEC, 30u64)
expect(fd_set_offset(3, 44u64)).to_equal(0)

expect(fd_prepare_fork_to_task(21u64)).to_equal(4u32)
expect(fd_get_refcount(3)).to_equal(2u32)

fd_activate_task(21u64)
expect(fd_is_valid(3)).to_equal(true)
expect(fd_get_cloexec(3)).to_equal(true)
expect(fd_get_offset(3)).to_equal(44u64)
expect(fd_set_offset(3, 88u64)).to_equal(0)

fd_activate_task(20u64)
expect(fd_get_offset(3)).to_equal(88u64)
```

</details>

#### releases inactive task descriptor contexts

1. fd table init
2. fd activate task
3. fd set
   - Expected: fd_prepare_fork_to_task(31u64) equals `4u32`
   - Expected: fd_get_refcount(3) equals `2u32`
   - Expected: fd_release_task(31u64) equals `4u32`
   - Expected: fd_get_refcount(3) equals `1u32`
4. fd activate task
   - Expected: fd_is_valid(3) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_activate_task(30u64)
fd_set(3, FD_TYPE_FILE, O_RDONLY, 40u64)
expect(fd_prepare_fork_to_task(31u64)).to_equal(4u32)
expect(fd_get_refcount(3)).to_equal(2u32)

expect(fd_release_task(31u64)).to_equal(4u32)
expect(fd_get_refcount(3)).to_equal(1u32)
fd_activate_task(31u64)
expect(fd_is_valid(3)).to_equal(false)
```

</details>

#### keeps duplicated open descriptions alive until the last close

1. fd table init
2. fd set
   - Expected: fd_set_offset(3, 55u64) equals `0`
   - Expected: dup_fd equals `4`
   - Expected: fd_close(3) equals `0`
   - Expected: fd_is_valid(3) is false
   - Expected: fd_is_valid(4) is true
   - Expected: fd_get_offset(4) equals `55u64`
   - Expected: fd_refcounts[4] equals `1u32`
   - Expected: fd_close(4) equals `0`
   - Expected: fd_is_valid(4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 10u64)
expect(fd_set_offset(3, 55u64)).to_equal(0)

val dup_fd = fd_dup(3)
expect(dup_fd).to_equal(4)
expect(fd_close(3)).to_equal(0)

expect(fd_is_valid(3)).to_equal(false)
expect(fd_is_valid(4)).to_equal(true)
expect(fd_get_offset(4)).to_equal(55u64)
expect(fd_refcounts[4]).to_equal(1u32)

expect(fd_close(4)).to_equal(0)
expect(fd_is_valid(4)).to_equal(false)
```

</details>

#### exposes fd backend metadata without direct table access

1. fd table init
2. fd set
   - Expected: fd_get_type(3) equals `FD_TYPE_FILE`
   - Expected: fd_get_backend_handle(3) equals `77u64`
   - Expected: fd_get_type(99) equals `FD_TYPE_FREE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 77u64)

expect(fd_get_type(3)).to_equal(FD_TYPE_FILE)
expect(fd_get_backend_handle(3)).to_equal(77u64)
expect(fd_get_type(99)).to_equal(FD_TYPE_FREE)
```

</details>

#### tracks readiness and notifications on the shared open description

1. fd table init
2. fd set
   - Expected: fd_set_poll_notification(3, POLLIN, 500u64) equals `0`
   - Expected: dup_fd equals `4`
   - Expected: fd_poll_notification(dup_fd, POLLIN) equals `500u64`
   - Expected: fd_poll_ready(dup_fd, POLLIN) equals `0 as i16`
   - Expected: fd_get_ready_generation(3) equals `0u64`
   - Expected: fd_update_ready(3, POLLIN, 0 as i16) equals `0`
   - Expected: fd_poll_ready(dup_fd, POLLIN) equals `POLLIN`
   - Expected: fd_get_ready_generation(dup_fd) equals `1u64`
   - Expected: fd_update_ready(dup_fd, POLLHUP, POLLIN) equals `0`
   - Expected: fd_poll_ready(3, POLLIN) equals `POLLHUP`
   - Expected: fd_get_ready_generation(3) equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_PIPE_READ, O_RDONLY, 11u64)
expect(fd_set_poll_notification(3, POLLIN, 500u64)).to_equal(0)

val dup_fd = fd_dup(3)
expect(dup_fd).to_equal(4)
expect(fd_poll_notification(dup_fd, POLLIN)).to_equal(500u64)
expect(fd_poll_ready(dup_fd, POLLIN)).to_equal(0 as i16)
expect(fd_get_ready_generation(3)).to_equal(0u64)

expect(fd_update_ready(3, POLLIN, 0 as i16)).to_equal(0)
expect(fd_poll_ready(dup_fd, POLLIN)).to_equal(POLLIN)
expect(fd_get_ready_generation(dup_fd)).to_equal(1u64)

expect(fd_update_ready(dup_fd, POLLHUP, POLLIN)).to_equal(0)
expect(fd_poll_ready(3, POLLIN)).to_equal(POLLHUP)
expect(fd_get_ready_generation(3)).to_equal(2u64)
```

</details>

#### reports invalid descriptors through poll readiness

1. fd table init
   - Expected: fd_poll_ready(99, POLLIN | POLLOUT) equals `POLLNVAL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()

expect(fd_poll_ready(99, POLLIN | POLLOUT)).to_equal(POLLNVAL)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
