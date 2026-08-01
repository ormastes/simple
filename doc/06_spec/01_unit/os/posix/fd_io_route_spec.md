# POSIX FD I/O Routing Specification

> SimpleOS native I/O is async-first. POSIX read/write/close wrappers must route

<!-- sdn-diagram:id=fd_io_route_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fd_io_route_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fd_io_route_spec -> std
fd_io_route_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fd_io_route_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# POSIX FD I/O Routing Specification

SimpleOS native I/O is async-first. POSIX read/write/close wrappers must route

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/posix/fd_io_route_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

SimpleOS native I/O is async-first. POSIX read/write/close wrappers must route
native pipe descriptors to the pipe backend, not through VFS IPC.

## Scenarios

### POSIX fd_io backend routing

#### routes file descriptors to the file backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fd_io_read_route(FD_TYPE_FILE)).to_equal(FD_IO_ROUTE_FILE)
expect(fd_io_write_route(FD_TYPE_FILE)).to_equal(FD_IO_ROUTE_FILE)
expect(fd_io_close_route(FD_TYPE_FILE)).to_equal(FD_IO_ROUTE_FILE)
```

</details>

#### routes serial descriptors to the serial backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fd_io_read_route(FD_TYPE_SERIAL)).to_equal(FD_IO_ROUTE_SERIAL)
expect(fd_io_write_route(FD_TYPE_SERIAL)).to_equal(FD_IO_ROUTE_SERIAL)
expect(fd_io_close_route(FD_TYPE_SERIAL)).to_equal(FD_IO_ROUTE_SERIAL)
```

</details>

#### routes pipe read descriptors to the pipe backend for read and close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fd_io_read_route(FD_TYPE_PIPE_READ)).to_equal(FD_IO_ROUTE_PIPE)
expect(fd_io_write_route(FD_TYPE_PIPE_READ)).to_equal(FD_IO_ROUTE_INVALID)
expect(fd_io_close_route(FD_TYPE_PIPE_READ)).to_equal(FD_IO_ROUTE_PIPE)
```

</details>

#### routes pipe write descriptors to the pipe backend for write and close

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fd_io_read_route(FD_TYPE_PIPE_WRITE)).to_equal(FD_IO_ROUTE_INVALID)
expect(fd_io_write_route(FD_TYPE_PIPE_WRITE)).to_equal(FD_IO_ROUTE_PIPE)
expect(fd_io_close_route(FD_TYPE_PIPE_WRITE)).to_equal(FD_IO_ROUTE_PIPE)
```

</details>

#### keeps socket descriptors on the compatibility route

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fd_io_read_route(FD_TYPE_SOCKET)).to_equal(FD_IO_ROUTE_SOCKET)
expect(fd_io_write_route(FD_TYPE_SOCKET)).to_equal(FD_IO_ROUTE_SOCKET)
expect(fd_io_close_route(FD_TYPE_SOCKET)).to_equal(FD_IO_ROUTE_SOCKET)
```

</details>

#### rejects free descriptors

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(fd_io_read_route(FD_TYPE_FREE)).to_equal(FD_IO_ROUTE_INVALID)
expect(fd_io_write_route(FD_TYPE_FREE)).to_equal(FD_IO_ROUTE_INVALID)
expect(fd_io_close_route(FD_TYPE_FREE)).to_equal(FD_IO_ROUTE_INVALID)
```

</details>

#### posix_dup2 keeps target unchanged when old fd is invalid

1. fd table init
2. fd set
   - Expected: fd_set_offset(4, 99u64) equals `0`
   - Expected: fd_set_cloexec(4, true) equals `0`
   - Expected: posix_dup2(99, 4) equals `-9`
   - Expected: fd_is_valid(4) is true
   - Expected: fd_ports[4] equals `44u64`
   - Expected: fd_get_offset(4) equals `99u64`
   - Expected: fd_get_cloexec(4) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(4, FD_TYPE_FILE, O_WRONLY, 44u64)
expect(fd_set_offset(4, 99u64)).to_equal(0)
expect(fd_set_cloexec(4, true)).to_equal(0)

expect(posix_dup2(99, 4)).to_equal(-9)

expect(fd_is_valid(4)).to_equal(true)
expect(fd_ports[4]).to_equal(44u64)
expect(fd_get_offset(4)).to_equal(99u64)
expect(fd_get_cloexec(4)).to_equal(true)
```

</details>

#### posix_dup2 replaces target through close semantics

1. fd table init
2. fd set
3. fd set
   - Expected: fd_set_offset(3, 7u64) equals `0`
   - Expected: fd_set_cloexec(4, true) equals `0`
   - Expected: posix_dup2(3, 4) equals `4`
   - Expected: fd_is_valid(4) is true
   - Expected: fd_ports[4] equals `33u64`
   - Expected: fd_get_offset(4) equals `7u64`
   - Expected: fd_get_cloexec(4) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDONLY, 33u64)
fd_set(4, FD_TYPE_FILE, O_WRONLY, 44u64)
expect(fd_set_offset(3, 7u64)).to_equal(0)
expect(fd_set_cloexec(4, true)).to_equal(0)

expect(posix_dup2(3, 4)).to_equal(4)

expect(fd_is_valid(4)).to_equal(true)
expect(fd_ports[4]).to_equal(33u64)
expect(fd_get_offset(4)).to_equal(7u64)
expect(fd_get_cloexec(4)).to_equal(false)
```

</details>

#### pread exact rejects invalid descriptors

1. fd table init
   - Expected: result.status equals `0 - EBADF as i64`
   - Expected: result.len equals `0u64`
   - Expected: result.data.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()

val result = posix_pread_exact_bytes(99, 0u64, 4u64)

expect(result.status).to_equal(0 - EBADF as i64)
expect(result.len).to_equal(0u64)
expect(result.data.len()).to_equal(0)
```

</details>

#### pread exact rejects non-file descriptors

1. fd table init
   - Expected: result.status equals `0 - EBADF as i64`
   - Expected: result.len equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()

val result = posix_pread_exact_bytes(0, 0u64, 1u64)

expect(result.status).to_equal(0 - EBADF as i64)
expect(result.len).to_equal(0u64)
```

</details>

#### pread exact rejects write-only file descriptors without moving offset

1. fd table init
2. fd set
   - Expected: fd_set_offset(3, 91u64) equals `0`
   - Expected: result.status equals `0 - EBADF as i64`
   - Expected: result.len equals `0u64`
   - Expected: fd_get_offset(3) equals `91u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_WRONLY, 33u64)
expect(fd_set_offset(3, 91u64)).to_equal(0)

val result = posix_pread_exact_bytes(3, 7u64, 8u64)

expect(result.status).to_equal(0 - EBADF as i64)
expect(result.len).to_equal(0u64)
expect(fd_get_offset(3)).to_equal(91u64)
```

</details>

#### pread exact restores offset for zero-byte file reads

1. fd table init
2. fd set
   - Expected: fd_set_offset(3, 91u64) equals `0`
   - Expected: result.status equals `0`
   - Expected: result.len equals `0u64`
   - Expected: result.data.len() equals `0`
   - Expected: fd_get_offset(3) equals `91u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fd_table_init()
fd_set(3, FD_TYPE_FILE, O_RDWR, 33u64)
expect(fd_set_offset(3, 91u64)).to_equal(0)

val result = posix_pread_exact_bytes(3, 7u64, 0u64)

expect(result.status).to_equal(0)
expect(result.len).to_equal(0u64)
expect(result.data.len()).to_equal(0)
expect(fd_get_offset(3)).to_equal(91u64)
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
