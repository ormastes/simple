# Async I/O Backend Routing Specification

> Native async I/O owns serial and VFS-backed file descriptor completion. Pipe

<!-- sdn-diagram:id=async_io_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_io_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_io_backend_spec -> std
async_io_backend_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_io_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async I/O Backend Routing Specification

Native async I/O owns serial and VFS-backed file descriptor completion. Pipe

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/posix/async_io_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Native async I/O owns serial and VFS-backed file descriptor completion. Pipe
descriptors remain owned by the native pipe backend and must not be treated as
VFS file descriptors.

## Scenarios

### async_io backend ownership

#### owns serial descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(async_io_backend_for_fd_type(FD_TYPE_SERIAL)).to_equal(ASYNC_IO_BACKEND_SERIAL)
```

</details>

#### owns VFS-backed file descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(async_io_backend_for_fd_type(FD_TYPE_FILE)).to_equal(ASYNC_IO_BACKEND_VFS)
```

</details>

#### does not own pipe descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(async_io_backend_for_fd_type(FD_TYPE_PIPE_READ)).to_equal(ASYNC_IO_BACKEND_INVALID)
expect(async_io_backend_for_fd_type(FD_TYPE_PIPE_WRITE)).to_equal(ASYNC_IO_BACKEND_INVALID)
```

</details>

#### rejects free descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(async_io_backend_for_fd_type(FD_TYPE_FREE)).to_equal(ASYNC_IO_BACKEND_INVALID)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
