# Syscall Dispatch Specification

> 1. expect eq

<!-- sdn-diagram:id=syscall_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Dispatch Specification

## Scenarios

### syscall dispatch numbers

#### core process syscalls have expected values

1. expect eq
2. expect eq
3. expect eq
4. expect eq
5. expect eq
6. expect eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_EXIT,           0)
expect_eq(SYS_YIELD,          1)
expect_eq(SYS_SPAWN,          2)
expect_eq(SYS_WAIT,           3)
expect_eq(SYS_GETPID,         4)
expect_eq(SYS_SPAWN_BINARY,   13)
```

</details>

#### SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct

1. expect true
2. expect true
3. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_true(SYS_EXIT != SYS_YIELD)
expect_true(SYS_EXIT != SYS_SPAWN_BINARY)
expect_true(SYS_YIELD != SYS_SPAWN_BINARY)
```

</details>

#### memory syscalls are in the 10-12 range

1. expect eq
2. expect eq
3. expect eq
4. expect true
5. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_MMAP,     10)
expect_eq(SYS_MUNMAP,   11)
expect_eq(SYS_MPROTECT, 12)
expect_true(SYS_MMAP < SYS_MUNMAP)
expect_true(SYS_MUNMAP < SYS_MPROTECT)
```

</details>

#### IPC syscalls start at 20

1. expect eq
2. expect eq
3. expect eq
4. expect eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_IPC_SEND,        20)
expect_eq(SYS_IPC_RECV,        21)
expect_eq(SYS_IPC_CREATE_PORT, 22)
expect_eq(SYS_IPC_CONNECT,     23)
```

</details>

#### file syscalls are in the 30-48 range

1. expect eq
2. expect eq
3. expect eq
4. expect true
5. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_FILE_OPEN,  30)
expect_eq(SYS_FILE_READ,  31)
expect_eq(SYS_FILE_WRITE, 32)
expect_true(SYS_FILE_OPEN < SYS_FILE_WRITE)
expect_true(SYS_FILE_WRITE < SYS_CHDIR)
```

</details>

#### debug_write is 60

1. expect eq


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_DEBUG_WRITE, 60)
```

</details>

#### POSIX libc syscall numbers are reserved

1. expect eq
2. expect eq
3. expect eq
4. expect eq
5. expect eq
6. expect eq
7. expect eq
8. expect eq
9. expect eq
10. expect eq
11. expect eq
12. expect true
13. expect true
14. expect true
15. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_POSIX_PROC_CREATE, 57)
expect_eq(SYS_POSIX_IMAGE_RUN, 59)
expect_eq(SYS_POSIX_CHILD_WAIT, 61)
expect_eq(SYS_POSIX_PIPE_PAIR, 62)
expect_eq(SYS_POSIX_FD_DUP2, 63)
expect_eq(SYS_POSIX_FD_DUP, 64)
expect_eq(SYS_DLOPEN, 65)
expect_eq(SYS_DLSYM, 66)
expect_eq(SYS_DLCLOSE, 67)
expect_eq(SYS_POSIX_POLL, 68)
expect_eq(SYS_POSIX_FCNTL, 69)
expect_true(SYS_SLEEP < SYS_POSIX_PROC_CREATE)
expect_true(SYS_POSIX_IMAGE_RUN < SYS_DEBUG_WRITE)
expect_true(SYS_DEBUG_WRITE < SYS_POSIX_CHILD_WAIT)
expect_true(SYS_POSIX_FCNTL < SYS_NET_SOCKET)
```

</details>

#### network syscalls are in the 70-77 range

1. expect eq
2. expect eq
3. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_NET_SOCKET,    70)
expect_eq(SYS_NET_IF_CONFIG, 77)
expect_true(SYS_NET_SOCKET < SYS_NET_IF_CONFIG)
```

</details>

#### device syscalls are in the 80-85 range

1. expect eq
2. expect eq
3. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_DEV_ENUMERATE, 80)
expect_eq(SYS_FREE_DMA,      85)
expect_true(SYS_DEV_ENUMERATE < SYS_FREE_DMA)
```

</details>

#### log and sysinfo syscalls are in 90-97 range

1. expect eq
2. expect eq
3. expect eq
4. expect eq
5. expect eq
6. expect true
7. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect_eq(SYS_LOG_WRITE,     90)
expect_eq(SYS_LOG_READ,      91)
expect_eq(SYS_SYSINFO,       95)
expect_eq(SYS_GET_HOSTNAME,  96)
expect_eq(SYS_SET_HOSTNAME,  97)
expect_true(SYS_LOG_WRITE < SYS_SYSINFO)
expect_true(SYS_GET_HOSTNAME != SYS_SET_HOSTNAME)
```

</details>

#### all primary syscall groups are non-overlapping

1. expect true
2. expect true
3. expect true
4. expect true
5. expect true
6. expect true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# process group max (13) < ipc group start (20)
expect_true(SYS_SPAWN_BINARY < SYS_IPC_SEND)
# ipc group max (29) < file group start (30)
expect_true(SYS_NOTIF_WAIT_ANY < SYS_FILE_OPEN)
# file group max (51) < debug (60)
expect_true(SYS_SLEEP < SYS_DEBUG_WRITE)
# debug (60) < net group start (70)
expect_true(SYS_DEBUG_WRITE < SYS_NET_SOCKET)
# net group max (77) < dev group start (80)
expect_true(SYS_NET_IF_CONFIG < SYS_DEV_ENUMERATE)
# dev group max (85) < log group start (90)
expect_true(SYS_FREE_DMA < SYS_LOG_WRITE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- syscall dispatch numbers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
