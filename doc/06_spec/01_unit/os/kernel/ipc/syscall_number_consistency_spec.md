# Syscall Number Consistency Specification

> Drift detector for the `SYS_IPC_*` constants duplicated across the kernel syscall dispatcher (`src/os/kernel/ipc/syscall.spl`) and every userland service that dispatches IPC syscalls (`wm_service`, `launcher`, `vfs`, `driver_supervisor`, `device_registry`, `netstack`, `userlib/window`, etc.).

<!-- sdn-diagram:id=syscall_number_consistency_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_number_consistency_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_number_consistency_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_number_consistency_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Number Consistency Specification

Drift detector for the `SYS_IPC_*` constants duplicated across the kernel syscall dispatcher (`src/os/kernel/ipc/syscall.spl`) and every userland service that dispatches IPC syscalls (`wm_service`, `launcher`, `vfs`, `driver_supervisor`, `device_registry`, `netstack`, `userlib/window`, etc.).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-006 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/01_research/local/ipc_error_38_2026-04-13.md |
| Source | `test/01_unit/os/kernel/ipc/syscall_number_consistency_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Drift detector for the `SYS_IPC_*` constants duplicated across the kernel
syscall dispatcher (`src/os/kernel/ipc/syscall.spl`) and every userland
service that dispatches IPC syscalls (`wm_service`, `launcher`, `vfs`,
`driver_supervisor`, `device_registry`, `netstack`, `userlib/window`, etc.).

The kernel dispatcher in `src/os/kernel/ipc/syscall.spl` is the canonical
source of truth:

    case 20: IpcSend         -> _handle_ipc_send
    case 21: IpcRecv         -> _handle_ipc_recv
    case 22: IpcCreatePort   -> _handle_ipc_create_port
    case 23: IpcConnect      -> _handle_ipc_connect

Historically several service modules declared `SYS_IPC_SEND = 23`, which
actually routed send traffic to the kernel's `IpcConnect` handler. This
spec asserts the canonical values and exists purely to prevent future
drift — if you change a `SYS_IPC_*` constant in any service, you must
update this spec (and the kernel dispatcher) to match.

## Scenarios

### SYS_IPC_* constant consistency across kernel and services

### kernel canonical values

#### SYS_IPC_SEND is 20

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SYS_IPC_SEND).to_equal(20 as u64)
```

</details>

#### SYS_IPC_RECV is 21

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SYS_IPC_RECV).to_equal(21 as u64)
```

</details>

#### SYS_IPC_CREATE_PORT is 22

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SYS_IPC_CREATE_PORT).to_equal(22 as u64)
```

</details>

#### SYS_IPC_CONNECT is 23

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SYS_IPC_CONNECT).to_equal(23 as u64)
```

</details>

#### SYS_BRK is 15

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SYS_BRK).to_equal(15 as u64)
```

</details>

#### SYS_REBOOT is 16

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SYS_REBOOT).to_equal(16 as u64)
```

</details>

#### SYS_SLEEP is 51

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(CANONICAL_SYS_SLEEP).to_equal(51 as u64)
```

</details>

### wm_service matches kernel

#### wm SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WM_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### wm SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WM_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### wm SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WM_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### wm SYS_IPC_CONNECT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(WM_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### launcher matches kernel

#### launcher SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LAUNCHER_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### launcher SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LAUNCHER_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### launcher SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LAUNCHER_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### launcher SYS_IPC_CONNECT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LAUNCHER_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### vfs_service matches kernel

#### vfs SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VFS_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### vfs SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VFS_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### vfs SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VFS_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### vfs SYS_IPC_CONNECT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(VFS_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### netstack matches kernel

#### netstack SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NETSTACK_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### netstack SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NETSTACK_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### netstack SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(NETSTACK_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

### driver_supervisor matches kernel

#### supervisor SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SUPERVISOR_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### supervisor SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SUPERVISOR_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### supervisor SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SUPERVISOR_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### supervisor SYS_SLEEP == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SUPERVISOR_SLEEP).to_equal(CANONICAL_SYS_SLEEP)
```

</details>

### device_registry matches kernel

#### registry SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(REGISTRY_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### registry SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(REGISTRY_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

### userlib/window matches kernel

#### userlib SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(USERLIB_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### userlib SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(USERLIB_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### userlib SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(USERLIB_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### userlib SYS_IPC_CONNECT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(USERLIB_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### driver_runtime matches kernel

#### driver runtime SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DRV_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### driver runtime SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DRV_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### driver runtime SYS_IPC_CREATE_PORT == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(DRV_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

### posix layer matches kernel

#### posix _SYS_IPC_SEND == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(POSIX_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### posix _SYS_IPC_RECV == canonical

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(POSIX_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** [doc/01_research/local/ipc_error_38_2026-04-13.md](doc/01_research/local/ipc_error_38_2026-04-13.md)


</details>
